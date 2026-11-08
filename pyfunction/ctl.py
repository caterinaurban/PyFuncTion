"""
CTL analysis (cf. main/CTLIterator.ml, the AST version of FuncTion's CTL
analysis, and frontend/CTLProperty.ml for the properties).

A CTL property is written as in FuncTion:

    p ::= atom | label: atom
        | AX{p} | AF{p} | AG{p} | AU{p}{p}
        | EX{p} | EF{p} | EG{p} | EU{p}{p}
        | AND{p}{p} | OR{p}{p} | NOT{p}

where an atom is a Python condition over the program variables (`x == 0
and y > 1`; the C notation `&&`, `||`, `!` and `true`/`false` is accepted
too), and `label: atom` holds only at the program points marked by a
`#LABEL: label` comment (e.g. `C1: true`).

The analysis is a backward analysis, by induction on the property: for each
subformula p, it computes at each program label a decision tree whose
domain is a set of states satisfying p (a sufficient condition), and whose
value bounds the number of steps before p holds (for the F and U
operators). The program satisfies the property if the tree at the entry is
defined on all the states satisfying the precondition.

  - atom: 0 where the atom holds, ⊥ elsewhere (`reset`);
  - AF{p} = AU{true}{p}, AU/EU: least fixpoints, as for termination: the
    leaves where p2 holds are reset to 0 (`until`), where neither p1 nor
    p2 holds they become ⊥;
  - AG/EG: greatest fixpoints, starting from the tree of p and cutting away
    the states that can (A) / must (E) leave it (`mask`, `dual_widen`);
  - AX/EX: one step backward from the tree of p;
  - AND, OR: meet and join of the trees, label by label;
  - NOT: the property is first put in negation normal form (nnf), so that
    NOT only applies to the atoms: NOT{atom} is the negated condition, and
    e.g. NOT{AF{p}} = EG{NOT{p}}, NOT{AU{p}{q}} = OR{EU{NOT{q}}{AND{NOT{p}}
    {NOT{q}}}}{EG{NOT{q}}}. A ⊥ leaf only means that a property is not
    proven, not that it does not hold, so the complement of a tree (⊥ <-> 0)
    would be unsound. With finite paths (below) the dualities hold in one
    direction only (e.g. EG{NOT{p}} implies NOT{AF{p}}, but a finite path
    where p never holds satisfies only the latter): sound, but incomplete.

As in FuncTion, a program exit (and the end of the program) has no
successor: no state satisfies a property there, so a finite path never
satisfies AG/EG, and AF p must reach p before the program ends.

Non-determinism: under the universal operators (A), the choices are made by
the environment (demonic), except for the variables listed in -angelic, whose
values are picked by the program (angelic, as for termination). Under the
existential operators (E) the path is existential, so every choice (x =
random.randint(a, b), x = input(), ...) is angelic, whatever -angelic lists.
The values that only approximate what the program computes (x ** y, unknown
calls) are always demonic, which is sound for both. Unlike FuncTion, where
the non-deterministic assignments make the existential properties undefined.
"""

import re
import time
from dataclasses import dataclass
from typing import Optional

from .syntax import Assign, Assume, If, While, Return, Label, BConst, negate
from .functions import APPROXIMATION, COMPUTATIONAL
from .termination import TerminationAnalysis, Timeout


# properties

@dataclass(frozen=True)
class Atomic:
    text: str  # the condition, as written
    label: Optional[str] = None
    cond: object = None  # the condition, translated (a BExp)
    negated: bool = False  # NOT{atom} (introduced by nnf)


@dataclass(frozen=True)
class Op:
    op: str  # AX AF AG AU EX EF EG EU AND OR NOT
    args: tuple


_UNARY = {'AX', 'AF', 'AG', 'EX', 'EF', 'EG', 'NOT'}
_BINARY = {'AU', 'EU', 'AND', 'OR'}
_OP_RE = re.compile(r'\s*(AX|AF|AG|AU|EX|EF|EG|EU|AND|OR|NOT)\s*\{')
_LABEL_RE = re.compile(r'\s*([A-Za-z_]\w*)\s*:(?!=)(.*)$', re.S)


class PropertyError(Exception):
    pass


def parse_property(text):
    """Parses a CTL property (the syntax of FuncTion); the atoms are left as
    text (see translate_property)."""
    pos = 0

    def prop():
        nonlocal pos
        m = _OP_RE.match(text, pos)
        if m:
            op = m.group(1)
            pos = m.end()
            args = [prop()]
            close()
            if op in _BINARY:
                m2 = re.compile(r'\s*\{').match(text, pos)
                if not m2:
                    raise PropertyError('%s needs two arguments: %s{...}{...}' % (op, op))
                pos = m2.end()
                args.append(prop())
                close()
            return Op(op, tuple(args))
        j = pos
        while j < len(text) and text[j] not in '{}':
            j += 1
        atom = text[pos:j].strip()
        if not atom:
            raise PropertyError('empty atomic proposition at position %d' % pos)
        if j < len(text) and text[j] == '{':
            raise PropertyError('unknown operator %r' % atom)
        pos = j
        m = _LABEL_RE.match(atom)
        if m:
            return Atomic(m.group(2).strip() or 'true', m.group(1))
        return Atomic(atom)

    def close():
        nonlocal pos
        m = re.compile(r'\s*\}').match(text, pos)
        if not m:
            raise PropertyError('expected } at position %d' % pos)
        pos = m.end()

    p = prop()
    if text[pos:].strip():
        raise PropertyError('unexpected text after the property: %r' % text[pos:].strip())
    return p


def _python_condition(text, variables):
    """The C notation of FuncTion's properties, in Python."""
    s = text.replace('&&', ' and ').replace('||', ' or ')
    s = re.sub(r'!(?!=)', ' not ', s)
    for w, v in (('true', 'True'), ('false', 'False')):
        if w not in variables:
            s = re.sub(r'\b%s\b' % w, v, s)
    return s.strip()


def translate_property(p, fe, program):
    """Translates the atoms of a property into conditions over the program
    variables (with the frontend fe)."""
    if isinstance(p, Atomic):
        return Atomic(p.text, p.label, fe.condition(_python_condition(p.text, program.variables), program),
                      p.negated)
    return Op(p.op, tuple(translate_property(a, fe, program) for a in p.args))


_DUAL = {'AX': 'EX', 'EX': 'AX', 'AF': 'EG', 'EG': 'AF', 'EF': 'AG', 'AG': 'EF', 'AND': 'OR', 'OR': 'AND'}


def nnf(p, neg=False):
    """The negation normal form of p (of NOT{p} if neg): NOT only applies to
    the atoms. With finite paths, the result implies the property (it is
    equivalent to it on the infinite paths)."""
    if isinstance(p, Atomic):
        return Atomic(p.text, p.label, p.cond, p.negated != neg)
    o, a = p.op, p.args
    if o == 'NOT':
        return nnf(a[0], not neg)
    if not neg:
        return Op(o, tuple(nnf(x) for x in a))
    if o in _DUAL:
        return Op(_DUAL[o], tuple(nnf(x, True) for x in a))
    # NOT{AU{p}{q}} = OR{EU{NOT q}{AND{NOT p}{NOT q}}}{EG{NOT q}}, and dually for EU
    u, g = ('EU', 'EG') if o == 'AU' else ('AU', 'AG')
    np, nq = nnf(a[0], True), nnf(a[1], True)
    return Op('OR', (Op(u, (nq, Op('AND', (np, nq)))), Op(g, (nq,))))


def property_str(p):
    if isinstance(p, Atomic):
        s = ('%s: %s' % (p.label, p.text)) if p.label else p.text
        return 'NOT{%s}' % s if p.negated else s
    return p.op + ''.join('{%s}' % property_str(a) for a in p.args)


def property_labels(p):
    if isinstance(p, Atomic):
        return {p.label} if p.label else set()
    return set().union(*(property_labels(a) for a in p.args))


def program_labels(block, out=None):
    """name -> the program labels ℓ of the Label statements with that name."""
    out = {} if out is None else out
    for l, s in block.stmts:
        if isinstance(s, Label):
            out.setdefault(s.name, []).append(l)
        elif isinstance(s, If):
            program_labels(s.then, out)
            program_labels(s.orelse, out)
        elif isinstance(s, While):
            program_labels(s.body, out)
    return out


def _first(b):
    return b.stmts[0][0] if b.stmts else b.end


UNIVERSAL, EXISTENTIAL = 'A', 'E'


class CTLAnalysis(TerminationAnalysis):
    """The CTL analysis; the forward analysis (for -refine) and the options
    are those of the termination analysis. `prop` is a translated property
    (translate_property)."""

    def __init__(self, program, prop, **kw):
        super().__init__(program, **kw)
        self.prop = prop
        self.formulas = []  # [(text, {label: tree})], in the order they are computed
        missing = property_labels(prop) - set(program_labels(program.body))
        self.warnings = ['label %s does not appear in the program (#LABEL: %s)' % (x, x) for x in sorted(missing)]

    # the abstract transformers of the two quantifiers

    def _join(self, q):
        return COMPUTATIONAL if q == EXISTENTIAL else APPROXIMATION

    def _assign(self, q, p, s):
        D = self.D
        if self._choice(s.value):
            if (s.target in self.angelic if q == UNIVERSAL else s.target not in self.program.approximations):
                return D.bwd_assign_angelic(p, s.target, s.value)
        return D.bwd_assign(p, s.target, s.value)

    def _filter(self, q, p, b):
        return self.D.filter(p, b, under=(q == EXISTENTIAL))

    def _check_time(self):
        if time.time() - self.start > self.timeout:
            raise Timeout()

    def _rec(self, kind, label, tree, **info):
        if self.record:
            self.record(kind, label, tree, **info)

    def _ref(self, p, l):
        return self.D.refine(p, self.fwd[l]) if self.refine else p

    def _labels(self, b, out):
        for l, s in b.stmts:
            out.append(l)
            if isinstance(s, If):
                self._labels(s.then, out)
                self._labels(s.orelse, out)
            elif isinstance(s, While):
                out.append(s.label)
                self._labels(s.body, out)
        out.append(b.end)
        return out

    # AU, EU (and AF, EF)

    def until(self, q, keep, reset):
        D = self.D
        inv = {}

        def d_until(t, l):
            return D.until(t, keep[l], reset[l])

        def blk(out, b):
            self._check_time()
            p = d_until(self._ref(out, b.end), b.end)
            inv[b.end] = p
            self._rec('label', b.end, p)
            for l, s in reversed(b.stmts):
                self._check_time()
                p = stm(p, s, l)
                p = d_until(self._ref(p, l), l)
                inv[l] = p
                self._rec('label', l, p, stmt=s)
            return p

        def stm(p, s, l):
            if isinstance(s, Label):
                return p
            if isinstance(s, Return):
                return D.bot()
            if isinstance(s, Assign):
                return self._assign(q, p, s)
            if isinstance(s, Assume):
                return self._filter(q, p, s.cond)
            if isinstance(s, If):
                p1 = self._filter(q, blk(p, s.then), s.cond)
                p2 = self._filter(q, blk(p, s.orelse), negate(s.cond))
                return D.join(self._join(q), p1, p2)
            if isinstance(s, While):
                h = s.label
                out_exit = self._filter(q, p, negate(s.cond))
                self._rec('exit', h, out_exit)
                i = D.seeded(self.seeds) if self.seeds else D.bot()
                self._rec('iteration', h, i, n=1, seeded=bool(self.seeds))
                out_enter = self._filter(q, blk(i, s.body), s.cond)
                n = 1
                while True:
                    self._rec('body', h, out_enter, n=n)
                    i1 = d_until(D.join(APPROXIMATION, out_exit, out_enter), l)
                    self._rec('join', h, i1, n=n, title='F(i) = until(body ⋎_A exit)')
                    if self.tracebwd:
                        self._trace('### %s:%d ###:\nout_exit: %s\nin: %s\nout_enter: %s\nin\': %s\n' % (
                            self._lbl(h), n, D.to_str(out_exit), D.to_str(i), D.to_str(out_enter), D.to_str(i1)))
                    leq_c = D.is_leq(COMPUTATIONAL, i1, i)
                    if leq_c and D.is_leq(APPROXIMATION, i1, i):
                        self._rec('fixpoint', h, i, n=n)
                        break
                    if n <= self.joinbwd:
                        i2 = i1
                    elif not leq_c:
                        i2 = D.widen(i, D.join(COMPUTATIONAL, i, i1))
                    else:
                        i2 = D.widen(i, i1)
                    self._rec('iteration', h, i2, n=n + 1, widened=n > self.joinbwd)
                    out_enter = self._filter(q, blk(i2, s.body), s.cond)
                    i = i2
                    n += 1
                inv[h] = i
                return i
            raise TypeError(s)

        blk(D.bot(), self.program.body)
        return inv

    # AG, EG

    def global_(self, q, fp):
        D = self.D
        inv = dict(fp)
        end = D.bot()

        def blk(out, b):
            self._check_time()
            p = D.mask(inv[b.end], self._ref(out, b.end))
            inv[b.end] = p
            self._rec('label', b.end, p)
            for l, s in reversed(b.stmts):
                self._check_time()
                cur = inv[l]
                p = self._ref(stm(cur, p, s), l)
                inv[l] = p
                self._rec('label', l, p, stmt=s)
            return p

        def stm(cur, p, s):
            if isinstance(s, Label):
                return D.mask(cur, p)
            if isinstance(s, Return):
                return end
            if isinstance(s, Assign):
                return D.mask(cur, self._assign(q, p, s))
            if isinstance(s, Assume):
                return D.mask(cur, self._filter(q, p, s.cond))
            if isinstance(s, If):
                p1 = self._filter(q, blk(p, s.then), s.cond)
                p2 = self._filter(q, blk(p, s.orelse), negate(s.cond))
                return D.mask(cur, D.join(self._join(q), p1, p2))
            if isinstance(s, While):
                h = s.label
                out_exit = self._filter(q, p, negate(s.cond))
                self._rec('exit', h, out_exit)
                ci = D.split(inv[h], self.seeds) if self.seeds else inv[h]
                self._rec('iteration', h, ci, n=1, seeded=bool(self.seeds),
                          title='iterate 1 = the tree of the property (start%s)' % (', split on the seeds' if self.seeds else ''))
                out_enter = self._filter(q, blk(ci, s.body), s.cond)
                n = 1
                while True:
                    self._rec('body', h, out_enter, n=n)
                    upd = D.mask(ci, D.join(self._join(q), out_exit, out_enter))
                    self._rec('join', h, upd, n=n, title='F(i) = mask(i, body ⋎ exit)')
                    if self.tracebwd:
                        self._trace('### %s:%d ###:\ncurrent_in: %s\nupdated_in: %s\n' % (
                            self._lbl(h), n, D.to_str(ci), D.to_str(upd)))
                    if D.is_leq(APPROXIMATION, ci, upd) and D.is_leq(COMPUTATIONAL, ci, upd):
                        self._rec('fixpoint', h, ci, n=n)
                        break
                    upd2 = upd if n <= self.joinbwd else D.dual_widen(ci, upd)
                    self._rec('iteration', h, upd2, n=n + 1, widened=n > self.joinbwd,
                              title='iterate %d%s' % (n + 1, ' (after dual widening)' if n > self.joinbwd else ''))
                    out_enter = self._filter(q, blk(upd2, s.body), s.cond)
                    ci = upd2
                    n += 1
                inv[h] = ci
                return ci
            raise TypeError(s)

        blk(end, self.program.body)
        return inv

    # AX, EX

    def next_(self, q, fp):
        D = self.D
        inv = {}

        def aux(b, outer):
            for k, (l, s) in enumerate(b.stmts):
                nl = b.stmts[k + 1][0] if k + 1 < len(b.stmts) else b.end
                ns = fp[nl]
                if isinstance(s, If):
                    s1 = self._filter(q, fp[_first(s.then)], s.cond)
                    s2 = self._filter(q, fp[_first(s.orelse)], negate(s.cond))
                    inv[l] = D.join(self._join(q), s1, s2)
                    aux(s.then, ns)
                    aux(s.orelse, ns)
                elif isinstance(s, While):
                    s1 = self._filter(q, fp[_first(s.body)], s.cond)
                    s2 = self._filter(q, ns, negate(s.cond))
                    inv[l] = inv[s.label] = D.join(self._join(q), s1, s2)
                    aux(s.body, fp[l])
                elif isinstance(s, Assign):
                    inv[l] = self._assign(q, ns, s)
                elif isinstance(s, Assume):
                    inv[l] = self._filter(q, ns, s.cond)
                elif isinstance(s, Return):
                    inv[l] = D.bot()
                else:
                    inv[l] = ns
            inv[b.end] = outer

        aux(self.program.body, D.bot())
        top = D.top()
        return {l: D.until(t, top, t) for l, t in inv.items()}  # the defined leaves become 0

    # atoms and boolean operators

    def atomic(self, b):
        t = self.D.reset(self.D.bot(), b)
        return {l: t for l in self.labels}

    def label_atomic(self, name, b, negated=False):
        """name: b holds at the labels name where b holds; NOT{name: b} at the
        labels name where b does not hold, and at all the other labels."""
        D = self.D
        at = set(program_labels(self.program.body).get(name, ()))
        if negated:
            t, other = D.reset(D.bot(), negate(b)), D.reset(D.bot(), BConst(True))
        else:
            t, other = D.reset(D.bot(), b), D.bot()
        return {l: (t if l in at else other) for l in self.labels}

    def compute(self, p):
        D = self.D
        true = self.atomic(BConst(True))

        def inv(p):
            if isinstance(p, Atomic):
                if p.label:
                    r = self.label_atomic(p.label, p.cond, p.negated)
                else:
                    r = self.atomic(negate(p.cond) if p.negated else p.cond)
            else:
                o, a = p.op, p.args
                if o == 'AX':
                    r = self.next_(UNIVERSAL, inv(a[0]))
                elif o == 'AF':
                    r = self.until(UNIVERSAL, true, inv(a[0]))
                elif o == 'AG':
                    r = self.global_(UNIVERSAL, inv(a[0]))
                elif o == 'AU':
                    r = self.until(UNIVERSAL, inv(a[0]), inv(a[1]))
                elif o == 'EU':
                    r = self.until(EXISTENTIAL, inv(a[0]), inv(a[1]))
                elif o == 'EF':
                    r = self.until(EXISTENTIAL, true, inv(a[0]))
                elif o == 'EG':
                    r = self.global_(EXISTENTIAL, inv(a[0]))
                elif o == 'EX':
                    r = self.next_(EXISTENTIAL, inv(a[0]))
                elif o == 'AND':
                    r1, r2 = inv(a[0]), inv(a[1])
                    r = {l: D.meet(COMPUTATIONAL, r1[l], r2[l]) for l in self.labels}
                elif o == 'OR':
                    r1, r2 = inv(a[0]), inv(a[1])
                    r = {l: D.join(COMPUTATIONAL, r1[l], r2[l]) for l in self.labels}
                else:  # NOT does not occur in negation normal form
                    raise ValueError(o)
            self.formulas.append((property_str(p), r))
            self._rec('formula', self.entry_label, r[self.entry_label], text=property_str(p),
                      k=len(self.formulas) - 1)
            return r

        return inv(nnf(p))

    def run(self, precondition=None):
        """Runs the analysis; returns True if the property is proven."""
        from .partition import Partition
        Partition.clear_caches()
        body = self.program.body
        self.labels = self._labels(body, [])
        self.entry_label = _first(body)
        self.start = time.time()
        # the forward analysis (the reachable states, used with -refine)
        if self.tracefwd:
            self._trace('\nForward Analysis Trace:\n')
        self.fwd_blk(self.B.top(self.env), body)
        self.start = time.time()
        if self.tracebwd:
            self._trace('\nBackward Analysis Trace:\n')
        self.bwd = self.compute(self.prop)
        self.entry = self.bwd[self.entry_label]
        cond = precondition if precondition is not None else BConst(True)
        return self.D.defined(self.entry, condition=cond)

    def backward_str(self):
        out = []
        for text, inv in self.formulas:
            out.append('Property: %s\n' % text)
            out.extend('%s:\n%s\n' % (self._lbl(l), self.D.to_str(inv[l])) for l in sorted(inv))
        return '\n'.join(out)
