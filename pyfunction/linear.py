"""
Linear constraints and linearization of program expressions
(cf. utils/Constraints.ml).

A constraint over the variables v_1, ..., v_n of an environment is an integer
tuple (a_1, ..., a_n, c) meaning a_1*v_1 + ... + a_n*v_n + c >= 0.

These are the constraints C labeling the decision nodes:

    C = { c_1*X_1 + ... + c_k*X_k + c_k+1 >= 0 | c_i ∈ Z, gcd(|c_1|, ..., |c_k+1|) = 1 }

in canonical form, equipped with a total order ≤_C: here, the lexicographic
order on the tuples (Python's tuple comparison), as in the OCaml
implementation. The decision trees are kept sorted with respect to ≤_C.

The second half of the module linearizes the program expressions.
"""

from fractions import Fraction
from math import gcd, lcm

from .syntax import Var, Const, Random, Interval, Neg, BinOp, Compare


class Env:
    """The (ordered) program variables."""

    def __init__(self, variables):
        self.vars = tuple(variables)
        self.n = len(self.vars)
        self.index = {v: i for i, v in enumerate(self.vars)}

    def unsat(self):
        return (0,) * self.n + (-1,)


# constraints

def tighten(c):
    """Normalizes a constraint over integer variables: the variable coefficients
    are made coprime and the constant is rounded down accordingly."""
    g = 0
    for x in c[:-1]:
        g = gcd(g, x)
    if g == 0:
        return c[:-1] + ((0 if c[-1] >= 0 else -1),)
    if g == 1:
        return c
    return tuple(x // g for x in c[:-1]) + (c[-1] // g,)


def negate(c):
    """Integer negation: not (e >= 0) is -e - 1 >= 0."""
    return tuple(-x for x in c[:-1]) + (-c[-1] - 1,)


def is_unsat(c):
    """⊥_C: a constraint without variables that is false (e.g. -1 >= 0)."""
    return not any(c[:-1]) and c[-1] < 0


def similar(c1, c2):
    """Constraints differing only for the constant."""
    return c1[:-1] == c2[:-1]


def mentions(c, i):
    return c[i] != 0


def _coeff_str(a, name, first):
    if a == 0:
        return ''
    sign = '-' if a < 0 else ('' if first else '+')
    a = abs(a)
    mag = '' if a == 1 else '%s*' % a
    if first:
        return '%s%s%s' % (sign, mag, name)
    return ' %s %s%s' % (sign, mag, name)


# printing

def linexpr_str(coeffs, const, names):
    """Pretty prints sum coeffs[i]*names[i] + const (coefficients may be fractions)."""
    out = ''
    for a, v in zip(coeffs, names):
        if a != 0:
            out += _coeff_str(a, v, out == '')
    if const != 0 or out == '':
        if out == '':
            out = str(const)
        else:
            out += ' %s %s' % ('-' if const < 0 else '+', abs(const))
    return out


def constraint_str(c, names):
    if is_unsat(c):
        return 'False'
    lhs = linexpr_str(c[:-1], 0, names) if any(c[:-1]) else '0'
    return '%s >= %s' % (lhs, -c[-1])


def canonical_str(c, names):
    """A constraint in canonical form, as on the slides: x - 6 >= 0."""
    if is_unsat(c):
        return 'False'
    return '%s >= 0' % linexpr_str(c[:-1], c[-1], names)


# linearization
#
# The abstract domains only handle linear expressions. An expression of the
# program (syntax.AExp) is turned into a linear form over the program
# variables and some fresh temporaries, together with linear constraints on
# the temporaries ("sides"). E.g.
#
#     x + [1, 2]   ->  x + t      with  t - 1 >= 0,  2 - t >= 0
#     x // 2       ->  t          with  x - 2t >= 0, 2t + 1 - x >= 0
#     x * y        ->  t          (no constraint: any value)
#
# The transfer functions then work in the space of the program variables
# extended with the temporaries, and project the temporaries away.

class LinForm:
    """A linear form sum coeffs[v]*v + const with integer coefficients."""

    __slots__ = ('coeffs', 'const')

    def __init__(self, coeffs=None, const=0):
        self.coeffs = coeffs or {}
        self.const = const

    def is_const(self):
        return not self.coeffs

    def add(self, other, k=1):
        coeffs = dict(self.coeffs)
        for v, a in other.coeffs.items():
            b = coeffs.get(v, 0) + k * a
            if b:
                coeffs[v] = b
            else:
                coeffs.pop(v, None)
        return LinForm(coeffs, self.const + k * other.const)

    def scale(self, k):
        if k == 0:
            return LinForm()
        return LinForm({v: k * a for v, a in self.coeffs.items()}, k * self.const)

    def vector(self, index, size):
        v = [0] * (size + 1)
        for x, a in self.coeffs.items():
            v[index[x]] += a
        v[size] = self.const
        return tuple(v)


class Linearizer:
    """Linearizes expressions, introducing fresh temporaries for the non-linear
    parts: x // c and x % c are encoded exactly with a temporary quotient,
    while other non-linear expressions become non-deterministic values."""

    def __init__(self):
        self.temps = []
        self.sides = []  # LinForms that must be >= 0

    def fresh(self):
        t = '~t%d' % len(self.temps)
        self.temps.append(t)
        return t

    def linearize(self, e):
        if isinstance(e, Var):
            return LinForm({e.name: 1})
        if isinstance(e, Const):
            return LinForm({}, e.value)
        if isinstance(e, Random):
            return LinForm({self.fresh(): 1})
        if isinstance(e, Interval):
            if isinstance(e.lo, Const) and e.lo == e.hi:
                return LinForm({}, e.lo.value)
            t = LinForm({self.fresh(): 1})
            if e.lo is not None:
                self.sides.append(t.add(self.linearize(e.lo), -1))
            if e.hi is not None:
                self.sides.append(self.linearize(e.hi).add(t, -1))
            return t
        if isinstance(e, Neg):
            return self.linearize(e.expr).scale(-1)
        if isinstance(e, BinOp):
            if e.op in ('+', '-'):
                l = self.linearize(e.left)
                r = self.linearize(e.right)
                return l.add(r, 1 if e.op == '+' else -1)
            if e.op == '*':
                l = self.linearize(e.left)
                r = self.linearize(e.right)
                if l.is_const():
                    return r.scale(l.const)
                if r.is_const():
                    return l.scale(r.const)
                return LinForm({self.fresh(): 1})
            if e.op in ('//', '%'):
                r = self.linearize(e.right)
                if not r.is_const() or r.const == 0:
                    return LinForm({self.fresh(): 1})
                c = r.const
                l = self.linearize(e.left)
                if l.is_const():
                    return LinForm({}, l.const // c if e.op == '//' else l.const % c)
                q = LinForm({self.fresh(): 1})
                rem = l.add(q, -c)  # l = c*q + rem
                if c > 0:  # 0 <= rem <= c - 1
                    self.sides.append(rem)
                    self.sides.append(LinForm({}, c - 1).add(rem, -1))
                else:  # c + 1 <= rem <= 0
                    self.sides.append(rem.scale(-1))
                    self.sides.append(rem.add(LinForm({}, c + 1), -1))
                return q if e.op == '//' else rem
        raise TypeError('unexpected expression %r' % (e,))

    def compare(self, b):
        """The constraint (as a LinForm >= 0) corresponding to a comparison."""
        assert isinstance(b, Compare)
        l = self.linearize(b.left)
        r = self.linearize(b.right)
        if b.op == '<':
            return r.add(l, -1).add(LinForm({}, -1))
        if b.op == '<=':
            return r.add(l, -1)
        if b.op == '>':
            return l.add(r, -1).add(LinForm({}, -1))
        if b.op == '>=':
            return l.add(r, -1)
        raise ValueError(b.op)


class Compiled:
    """A linearized expression over the environment variables followed by the
    temporaries: expr is a homogenized vector, sides are inequalities."""

    __slots__ = ('ntemps', 'expr', 'sides')

    def __init__(self, ntemps, expr, sides):
        self.ntemps = ntemps
        self.expr = expr
        self.sides = sides


def _compile(env, lin, form):
    names = list(env.vars) + lin.temps
    index = {v: i for i, v in enumerate(names)}
    size = len(names)
    expr = form.vector(index, size)
    sides = [s.vector(index, size) for s in lin.sides]
    return Compiled(len(lin.temps), expr, sides)


def compile_aexp(env, e):
    lin = Linearizer()
    form = lin.linearize(e)
    return _compile(env, lin, form)


def compile_compare(env, b):
    lin = Linearizer()
    form = lin.compare(b)
    return _compile(env, lin, form)


def to_fractions(v):
    return tuple(Fraction(x) for x in v)


def integer_vector(coeffs, const):
    """Scales a rational vector to an integer one; returns (vector, multiplier)."""
    m = 1
    for x in list(coeffs) + [const]:
        m = lcm(m, Fraction(x).denominator)
    return tuple(int(x * m) for x in coeffs) + (int(const * m),), m
