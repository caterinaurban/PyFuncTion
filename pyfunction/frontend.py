"""
Python frontend: translates (a numerical subset of) Python into the abstract
syntax of syntax.py, using the standard `ast` module.

Supported:
  - integer variables, integer literals, True/False
  - arithmetic: + - * // % unary - and +, ~ ; boolean: and or not,
    comparisons (also chained), conditional expressions
  - statements: assignments (also augmented, annotated, chained, and tuple
    assignments), if/elif/else, while, for over range(...) with a constant
    step, pass, return, assert, raise, exit()
  - calls to non-recursive functions defined in the same module (inlined)
  - non-determinism: random.randint(a, b), random.randrange(a, b), input(),
    and calls to unknown functions; assume(cond) restricts the executions
  - abs(...), min(...), max(...)

The analyzed entry point is a function (main by default), whose parameters
are the (unknown) inputs of the program; without such a function, the module
top-level code is analyzed. Uninitialized variables have unknown values.

How the translation works: each Python expression is translated into a pair
(statements, expression): the statements compute the parts of the expression
that are not expressions of the abstract syntax (calls of inlined functions,
abs/min/max, conditional expressions...) into fresh temporary variables
(named tmp#k), and the expression refers to them. E.g.

    y = x - get_step(x)    becomes    get_step#1.x = x
                                      if get_step#1.x > 10:
                                          get_step#1.return = 2
                                      else:
                                          get_step#1.return = 1
                                      y = x - get_step#1.return

The names of the generated variables contain # or ., so they cannot clash
with Python identifiers.
"""

import ast

from .syntax import (Var, Const, Random, Interval, Neg, BinOp, BConst, Maybe,
                     Not, BoolOp, Compare, Assign, Assume, If, While, Return,
                     Program, label_program)

_BEXP = (BConst, Maybe, Not, BoolOp, Compare)


class UnsupportedError(Exception):

    def __init__(self, msg, node=None):
        if node is not None and hasattr(node, 'lineno'):
            msg = 'line %d: %s' % (node.lineno, msg)
        super().__init__(msg)


_arith_ops = {ast.Add: '+', ast.Sub: '-', ast.Mult: '*', ast.FloorDiv: '//', ast.Mod: '%'}
_cmp_ops = {ast.Lt: '<', ast.LtE: '<=', ast.Gt: '>', ast.GtE: '>='}

_NONDET_FUNCS = {'input', 'nondet', 'nondet_int', '__VERIFIER_nondet_int', 'getrandbits'}
_ASSUME_FUNCS = {'assume', '__VERIFIER_assume'}
_EXIT_FUNCS = {'exit', 'quit', '_exit'}
_IGNORED_FUNCS = {'print'}


def _fold(op, a, b):
    if op == '+':
        return a + b
    if op == '-':
        return a - b
    if op == '*':
        return a * b
    if op == '//':
        return a // b
    if op == '%':
        return a % b
    raise ValueError(op)


def _call_name(func):
    """The (unqualified) name of the called function, e.g. randint for random.randint."""
    if isinstance(func, ast.Name):
        return func.id
    if isinstance(func, ast.Attribute):
        return func.attr
    return None


def _contains(nodes, types):
    for n in nodes:
        for m in ast.walk(n):
            if isinstance(m, types):
                return True
    return False


def _assigned_names(fdef):
    names = set()
    for n in ast.walk(fdef):
        if isinstance(n, ast.Name) and isinstance(n.ctx, ast.Store):
            names.add(n.id)
    return names


class _Context:
    """Translation context: the renaming of the variables (for inlined
    functions) and the stack of the functions being inlined."""

    def __init__(self, renaming=None, stack=(), function=None):
        self.renaming = renaming or {}
        self.stack = stack
        self.function = function  # name of the inlined function, None for the entry point

    def var(self, name):
        return self.renaming.get(name, name)


class Frontend:

    def __init__(self, source, entry='main', filename='<input>'):
        self.source = source
        self.entry = entry
        self.filename = filename
        self.funcs = {}
        self.counter = 0
        self.inlined = 0
        self.warnings = []

    # entry point

    def translate(self):
        try:
            module = ast.parse(self.source, filename=self.filename)
        except SyntaxError as e:
            raise UnsupportedError('syntax error: %s' % e)
        toplevel = []
        for s in module.body:
            if isinstance(s, ast.FunctionDef):
                self.funcs[s.name] = s
            elif isinstance(s, (ast.Import, ast.ImportFrom)):
                continue
            elif isinstance(s, ast.Expr) and isinstance(s.value, ast.Constant) and isinstance(s.value.value, str):
                continue  # docstring
            else:
                toplevel.append(s)
        ctx = _Context()
        if self.entry in self.funcs:
            fdef = self.funcs[self.entry]
            inputs = self._params(fdef)
            stmts = []
            for s in toplevel:  # global initializations
                if isinstance(s, (ast.Assign, ast.AnnAssign, ast.AugAssign)):
                    stmts.extend(self.stmt(s, ctx))
            ctx = _Context(stack=(self.entry,))
            stmts.extend(self.stmts(fdef.body, ctx))
        else:
            inputs = []
            stmts = []
            for s in toplevel:
                if self._is_main_guard(s):
                    stmts.extend(self.stmts(s.body, ctx))
                else:
                    stmts.extend(self.stmt(s, ctx))
        body = label_program(stmts)
        variables = list(inputs)
        seen = set(variables)
        for v in self._variables(body):
            if v not in seen:
                seen.add(v)
                variables.append(v)
        return Program(variables, inputs, body)

    def condition(self, text, program):
        """Translates a boolean condition over the program variables (e.g. a precondition)."""
        try:
            node = ast.parse(text, mode='eval').body
        except SyntaxError as e:
            raise UnsupportedError('syntax error in condition: %s' % e)
        for n in ast.walk(node):
            if isinstance(n, ast.Name) and n.id not in program.variables:
                raise UnsupportedError('unknown variable %s in condition' % n.id)
            if isinstance(n, ast.Call):
                raise UnsupportedError('calls are not allowed in conditions')
        pre, b = self.bexp(node, _Context())
        assert not pre
        return b

    # helpers

    def fresh(self, base='tmp'):
        self.counter += 1
        return '%s#%d' % (base, self.counter)

    @staticmethod
    def _params(fdef):
        a = fdef.args
        if a.vararg or a.kwarg:
            raise UnsupportedError('variadic parameters are not supported', fdef)
        return [p.arg for p in a.posonlyargs + a.args + a.kwonlyargs]

    @staticmethod
    def _is_main_guard(s):
        if not isinstance(s, ast.If):
            return False
        t = s.test
        return (isinstance(t, ast.Compare) and isinstance(t.left, ast.Name) and t.left.id == '__name__'
                and len(t.ops) == 1 and isinstance(t.ops[0], ast.Eq))

    @staticmethod
    def _variables(block):
        out = []

        def aexp(e):
            if isinstance(e, Var):
                out.append(e.name)
            elif isinstance(e, Neg):
                aexp(e.expr)
            elif isinstance(e, BinOp):
                aexp(e.left)
                aexp(e.right)

        def bexp(b):
            if isinstance(b, Not):
                bexp(b.expr)
            elif isinstance(b, BoolOp):
                bexp(b.left)
                bexp(b.right)
            elif isinstance(b, Compare):
                aexp(b.left)
                aexp(b.right)

        def blk(b):
            for _, s in b.stmts:
                if isinstance(s, Assign):
                    out.append(s.target)
                    aexp(s.value)
                elif isinstance(s, Assume):
                    bexp(s.cond)
                elif isinstance(s, If):
                    bexp(s.cond)
                    blk(s.then)
                    blk(s.orelse)
                elif isinstance(s, While):
                    bexp(s.cond)
                    blk(s.body)

        blk(block)
        return out

    # statements

    def stmts(self, ss, ctx):
        out = []
        for s in ss:
            out.extend(self.stmt(s, ctx))
        return out

    def assign(self, target, value):
        """Assignment of an arithmetic or boolean value to a variable."""
        if isinstance(value, _BEXP):
            return [If(value, [Assign(target, Const(1))], [Assign(target, Const(0))])]
        return [Assign(target, value)]

    def stmt(self, s, ctx):
        if isinstance(s, ast.Assign):
            targets = s.targets
            if isinstance(s.value, ast.Tuple):
                return self._tuple_assign(s, ctx)
            pre, v = self.expr(s.value, ctx)
            out = list(pre)
            if len(targets) == 1 and isinstance(targets[0], ast.Name):
                return out + self.assign(ctx.var(targets[0].id), v)
            if all(isinstance(t, ast.Name) for t in targets):  # a = b = e
                first = ctx.var(targets[0].id)
                out += self.assign(first, v)
                for t in targets[1:]:
                    out.append(Assign(ctx.var(t.id), Var(first)))
                return out
            raise UnsupportedError('unsupported assignment target', s)
        if isinstance(s, ast.AugAssign):
            if not isinstance(s.target, ast.Name):
                raise UnsupportedError('unsupported assignment target', s)
            op = _arith_ops.get(type(s.op))
            if op is None:
                raise UnsupportedError('unsupported operator %s' % type(s.op).__name__, s)
            pre, v = self.aexp(s.value, ctx)
            x = ctx.var(s.target.id)
            return list(pre) + [Assign(x, self._binop(op, Var(x), v))]
        if isinstance(s, ast.AnnAssign):
            if not isinstance(s.target, ast.Name):
                raise UnsupportedError('unsupported assignment target', s)
            if s.value is None:
                return []
            pre, v = self.expr(s.value, ctx)
            return list(pre) + self.assign(ctx.var(s.target.id), v)
        if isinstance(s, ast.If):
            pre, c = self.bexp(s.test, ctx)
            return list(pre) + [If(c, self.stmts(s.body, ctx), self.stmts(s.orelse, ctx))]
        if isinstance(s, ast.While):
            if s.orelse:
                raise UnsupportedError('while ... else is not supported', s)
            self._check_loop_body(s)
            pre, c = self.bexp(s.test, ctx)
            body = self.stmts(s.body, ctx)
            # the statements computing the condition are executed before the
            # loop and again at the end of each iteration
            return list(pre) + [While(c, body + list(pre))]
        if isinstance(s, ast.For):
            return self._for(s, ctx)
        if isinstance(s, ast.Pass):
            return []
        if isinstance(s, ast.Expr):
            return self._expr_stmt(s, ctx)
        if isinstance(s, ast.Return):
            if ctx.function is not None:
                raise UnsupportedError('return inside a loop of an inlined function is not supported', s)
            pre = []
            if s.value is not None:
                pre, _ = self.expr(s.value, ctx)
            return list(pre) + [Return()]
        if isinstance(s, ast.Assert):
            # a failing assertion raises an exception: the program stops
            pre, c = self.bexp(s.test, ctx)
            return list(pre) + [If(c, [], [Return()])]
        if isinstance(s, ast.Raise):
            return [Return()]
        if isinstance(s, (ast.Break, ast.Continue)):
            raise UnsupportedError('%s is not supported' % type(s).__name__.lower(), s)
        if isinstance(s, (ast.Import, ast.ImportFrom)):
            return []
        raise UnsupportedError('unsupported statement %s' % type(s).__name__, s)

    def _tuple_assign(self, s, ctx):
        """Simultaneous assignment a, b = e1, e2."""
        if not (len(s.targets) == 1 and isinstance(s.targets[0], ast.Tuple)
                and len(s.targets[0].elts) == len(s.value.elts)
                and all(isinstance(t, ast.Name) for t in s.targets[0].elts)):
            raise UnsupportedError('unsupported tuple assignment', s)
        out = []
        temps = []
        for e in s.value.elts:
            pre, v = self.expr(e, ctx)
            t = self.fresh()
            out += list(pre) + self.assign(t, v)
            temps.append(t)
        for x, t in zip(s.targets[0].elts, temps):
            out.append(Assign(ctx.var(x.id), Var(t)))
        return out

    def _check_loop_body(self, s):
        for n in s.body:
            for m in ast.walk(n):
                if isinstance(m, (ast.Break, ast.Continue)):
                    raise UnsupportedError('%s is not supported' % type(m).__name__.lower(), m)

    def _for(self, s, ctx):
        """for v in range(a, b, step): body   becomes

            for#k = a; end#k = b
            while for#k < end#k:      (> if step < 0)
                v = for#k
                body
                for#k = for#k + step

        As in Python, the bound is evaluated once, and assigning v in the
        body does not change the number of iterations."""
        if s.orelse:
            raise UnsupportedError('for ... else is not supported', s)
        it = s.iter
        if not (isinstance(it, ast.Call) and _call_name(it.func) == 'range' and 1 <= len(it.args) <= 3
                and not it.keywords):
            raise UnsupportedError('only for loops over range(...) are supported', s)
        if not isinstance(s.target, ast.Name):
            raise UnsupportedError('unsupported for loop target', s)
        self._check_loop_body(s)
        args = it.args
        out = []
        if len(args) == 1:
            start, (pre, stop) = Const(0), self.aexp(args[0], ctx)
            out += pre
        else:
            pre, start = self.aexp(args[0], ctx)
            out += pre
            pre, stop = self.aexp(args[1], ctx)
            out += pre
        step = 1
        if len(args) == 3:
            pre, st = self.aexp(args[2], ctx)
            if pre or not isinstance(st, Const) or st.value == 0:
                raise UnsupportedError('the step of range(...) must be a non-zero integer constant', s)
            step = st.value
        counter = self.fresh('for')
        bound = self.fresh('end')
        out.append(Assign(counter, start))
        out.append(Assign(bound, stop))
        cond = Compare('<' if step > 0 else '>', Var(counter), Var(bound))
        body = [Assign(ctx.var(s.target.id), Var(counter))]
        body += self.stmts(s.body, ctx)
        body.append(Assign(counter, BinOp('+', Var(counter), Const(step))))
        out.append(While(cond, body))
        return out

    def _expr_stmt(self, s, ctx):
        e = s.value
        if isinstance(e, ast.Constant):
            return []
        if isinstance(e, ast.Call):
            name = _call_name(e.func)
            if name in _ASSUME_FUNCS and len(e.args) == 1:
                pre, c = self.bexp(e.args[0], ctx)
                return list(pre) + [Assume(c)]
            if name in _EXIT_FUNCS:
                return [Return()]
            if name in _IGNORED_FUNCS or (name not in self.funcs):
                out = []
                for a in e.args:  # arguments are still evaluated
                    pre, _ = self.expr(a, ctx)
                    out += pre
                return out
            pre, _ = self.expr(e, ctx)
            return list(pre)
        pre, _ = self.expr(e, ctx)
        return list(pre)

    # expressions

    def aexp(self, e, ctx):
        """Translates an arithmetic expression: returns (statements, AExp)."""
        pre, v = self.expr(e, ctx)
        if isinstance(v, BConst):
            return pre, Const(1 if v.value else 0)
        if isinstance(v, _BEXP):
            t = self.fresh()
            return list(pre) + self.assign(t, v), Var(t)
        return pre, v

    def bexp(self, e, ctx):
        """Translates a boolean expression: returns (statements, BExp)."""
        pre, v = self.expr(e, ctx)
        if isinstance(v, _BEXP):
            return pre, v
        if isinstance(v, Const):
            return pre, BConst(v.value != 0)
        return pre, BoolOp('or', Compare('<', v, Const(0)), Compare('>', v, Const(0)))

    @staticmethod
    def _binop(op, l, r):
        if isinstance(l, Const) and isinstance(r, Const):
            if op in ('//', '%') and r.value == 0:
                return Random()
            return Const(_fold(op, l.value, r.value))
        return BinOp(op, l, r)

    def expr(self, e, ctx):
        if isinstance(e, ast.Constant):
            if isinstance(e.value, bool):
                return [], BConst(e.value)
            if isinstance(e.value, int):
                return [], Const(e.value)
            raise UnsupportedError('unsupported constant %r (only integers are supported)' % (e.value,), e)
        if isinstance(e, ast.Name):
            return [], Var(ctx.var(e.id))
        if isinstance(e, ast.UnaryOp):
            if isinstance(e.op, ast.Not):
                pre, b = self.bexp(e.operand, ctx)
                return pre, Not(b)
            pre, v = self.aexp(e.operand, ctx)
            if isinstance(e.op, ast.UAdd):
                return pre, v
            if isinstance(e.op, ast.USub):
                return pre, Const(-v.value) if isinstance(v, Const) else Neg(v)
            if isinstance(e.op, ast.Invert):  # ~x = -x - 1
                return pre, self._binop('-', Const(-v.value) if isinstance(v, Const) else Neg(v), Const(1))
        if isinstance(e, ast.BinOp):
            op = _arith_ops.get(type(e.op))
            pre1, l = self.aexp(e.left, ctx)
            pre2, r = self.aexp(e.right, ctx)
            if op is None:
                if isinstance(e.op, ast.Pow):
                    if isinstance(l, Const) and isinstance(r, Const) and r.value >= 0:
                        return pre1 + pre2, Const(l.value ** r.value)
                    return pre1 + pre2, Random()
                if isinstance(e.op, ast.Div):
                    raise UnsupportedError('true division / is not supported (use //)', e)
                raise UnsupportedError('unsupported operator %s' % type(e.op).__name__, e)
            if op == '%' and not isinstance(r, Const):
                # Python semantics: the result has the sign of the divisor
                # and is smaller in absolute value; x % 0 raises an exception
                t = self.fresh()
                pos = Assign(t, Interval(Const(0), BinOp('-', r, Const(1))))
                neg = Assign(t, Interval(BinOp('+', r, Const(1)), Const(0)))
                check = If(Compare('>', r, Const(0)), [pos],
                           [If(Compare('<', r, Const(0)), [neg], [Return()])])
                return pre1 + pre2 + [check], Var(t)
            return pre1 + pre2, self._binop(op, l, r)
        if isinstance(e, ast.BoolOp):
            op = 'and' if isinstance(e.op, ast.And) else 'or'
            pre, res = self.bexp(e.values[0], ctx)
            for v in e.values[1:]:
                p, b = self.bexp(v, ctx)
                pre = pre + p
                res = BoolOp(op, res, b)
            return pre, res
        if isinstance(e, ast.Compare):
            pre, left = self.aexp(e.left, ctx)
            res = None
            for op, right in zip(e.ops, e.comparators):
                p, r = self.aexp(right, ctx)
                pre = pre + p
                c = self._compare(op, left, r, e)
                res = c if res is None else BoolOp('and', res, c)
                left = r
            return pre, res
        if isinstance(e, ast.IfExp):
            pre, c = self.bexp(e.test, ctx)
            t = self.fresh()
            p1, v1 = self.expr(e.body, ctx)
            p2, v2 = self.expr(e.orelse, ctx)
            return list(pre) + [If(c, list(p1) + self.assign(t, v1), list(p2) + self.assign(t, v2))], Var(t)
        if isinstance(e, ast.Call):
            return self._call(e, ctx)
        raise UnsupportedError('unsupported expression %s' % type(e).__name__, e)

    def _compare(self, op, l, r, node):
        if isinstance(op, ast.Eq):
            if isinstance(l, Const) and isinstance(r, Const):
                return BConst(l.value == r.value)
            return BoolOp('and', Compare('<=', l, r), Compare('>=', l, r))
        if isinstance(op, ast.NotEq):
            if isinstance(l, Const) and isinstance(r, Const):
                return BConst(l.value != r.value)
            return BoolOp('or', Compare('<', l, r), Compare('>', l, r))
        o = _cmp_ops.get(type(op))
        if o is None:
            raise UnsupportedError('unsupported comparison %s' % type(op).__name__, node)
        if isinstance(l, Const) and isinstance(r, Const):
            return BConst({'<': l.value < r.value, '<=': l.value <= r.value,
                           '>': l.value > r.value, '>=': l.value >= r.value}[o])
        return Compare(o, l, r)

    def _call(self, e, ctx):
        name = _call_name(e.func)
        if isinstance(e.func, ast.Name) and name in self.funcs:
            return self._inline(e, ctx)
        if name in ('randint', 'randrange') and len(e.args) == 2:
            pre1, lo = self.aexp(e.args[0], ctx)
            pre2, hi = self.aexp(e.args[1], ctx)
            if name == 'randrange':
                hi = self._binop('-', hi, Const(1))
            return pre1 + pre2, Interval(lo, hi)
        if name == 'int' and len(e.args) == 1:
            return self.aexp(e.args[0], ctx)
        if name == 'abs' and len(e.args) == 1:
            pre, v = self.aexp(e.args[0], ctx)
            if isinstance(v, Const):
                return pre, Const(abs(v.value))
            t = self.fresh()
            return list(pre) + [If(Compare('>=', v, Const(0)), [Assign(t, v)], [Assign(t, Neg(v))])], Var(t)
        if name in ('min', 'max') and len(e.args) >= 2:
            pre, res = self.aexp(e.args[0], ctx)
            pre = list(pre)
            for a in e.args[1:]:
                p, v = self.aexp(a, ctx)
                pre += p
                t = self.fresh()
                op = '<=' if name == 'min' else '>='
                pre.append(If(Compare(op, res, v), [Assign(t, res)], [Assign(t, v)]))
                res = Var(t)
            return pre, res
        if name == 'bool' and len(e.args) == 1:
            return self.bexp(e.args[0], ctx)
        pre = []
        for a in e.args:  # arguments are still evaluated
            p, _ = self.expr(a, ctx)
            pre += p
        if name not in _NONDET_FUNCS:
            self.warnings.append('line %d: call to unknown function %s approximated by a '
                                 'non-deterministic value' % (e.lineno, name or '?'))
        return pre, Random()

    def _inline(self, e, ctx):
        name = e.func.id
        if name in ctx.stack:
            raise UnsupportedError('recursive function %s is not supported' % name, e)
        fdef = self.funcs[name]
        params = self._params(fdef)
        self.inlined += 1
        prefix = '%s#%d.' % (name, self.inlined)
        locals_ = set(params) | _assigned_names(fdef)
        renaming = {x: prefix + x for x in locals_}
        callee = _Context(renaming, ctx.stack + (name,), name)
        # bind the arguments
        values = {}
        if len(e.args) > len(params):
            raise UnsupportedError('too many arguments in call to %s' % name, e)
        pre = []
        for p, a in zip(params, e.args):
            values[p] = a
        for k in e.keywords:
            if k.arg not in params:
                raise UnsupportedError('unexpected keyword argument %s' % k.arg, e)
            values[k.arg] = k.value
        defaults = fdef.args.defaults
        for p, d in zip(params[len(params) - len(defaults):], defaults):
            values.setdefault(p, d)
        for p in params:
            if p not in values:
                raise UnsupportedError('missing argument %s in call to %s' % (p, name), e)
            pr, v = self.aexp(values[p], ctx if values[p] not in defaults else _Context())
            pre += pr
            pre.append(Assign(renaming[p], v))
        ret = prefix + 'return'
        pre += self._callee_body(fdef.body, callee, ret)
        return pre, Var(ret)

    def _callee_body(self, ss, ctx, ret):
        """Translates the body of an inlined function: `return e` assigns e to
        the return variable, and the remaining statements are moved inside the
        branches of the conditionals containing a return."""
        out = []
        for i, s in enumerate(ss):
            if isinstance(s, ast.FunctionDef):
                raise UnsupportedError('nested functions are not supported', s)
            if isinstance(s, ast.Return):
                if s.value is not None:
                    pre, v = self.expr(s.value, ctx)
                    out += list(pre) + self.assign(ret, v)
                return out
            if _contains([s], ast.Return):
                if isinstance(s, ast.If):
                    rest = ss[i + 1:]
                    pre, c = self.bexp(s.test, ctx)
                    out += list(pre) + [If(c, self._callee_body(s.body + rest, ctx, ret),
                                           self._callee_body(s.orelse + rest, ctx, ret))]
                    return out
                raise UnsupportedError('return inside a loop of an inlined function is not supported', s)
            out += self.stmt(s, ctx)
        return out


def parse_program(source, entry='main', filename='<input>'):
    """Parses Python source code into a labeled Program; returns (program, frontend)."""
    fe = Frontend(source, entry, filename)
    return fe.translate(), fe
