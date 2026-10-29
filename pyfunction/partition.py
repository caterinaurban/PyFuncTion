"""
The numerical abstract domain D, used:

  - by the forward analysis, to over-approximate the reachable states R♮;
  - by the decision trees, as the "linear constraints auxiliary abstract
    domain": the set C of constraints along a path of a tree is turned into
    an element α_C(C) of D (`inner`), and an element of D is turned back
    into a set of constraints γ_C (`constraints`), e.g.

        X ↦ [-∞, 3], Y ↦ [0, +∞]   <->   { 3 - X >= 0, Y >= 0 }

(cf. domains/Partition.ml and domains/Numerical.ml). Three domains are
provided, all built on the exact polyhedra of polyhedra.py:

  - Box:        intervals (non-relational)
  - Octagon:    constraints of the form ±x ± y <= c
  - Polyhedra:  conjunctions of arbitrary linear inequalities

Each domain provides the lattice operations (⊑_D is_leq, ⊔_D join, ⊓_D meet,
▿_D widen), and the transfer functions ASSIGN_D (fwd_assign), the backward
assignment ASSIGN←_D (bwd_assign), and FILTER_D (filter).

Program variables are integers: constraints are tightened accordingly (e.g.
2x >= 3 becomes x >= 2).
"""

from fractions import Fraction
from math import floor, ceil, gcd

from .polyhedra import Polyhedron
from .linear import (tighten, is_unsat, constraint_str, linexpr_str,
                     compile_aexp, compile_compare)
from .syntax import BConst, Maybe, Not, BoolOp, Compare, negate as negate_bexp


# Transfer functions on polyhedra, shared by the three domains. The
# expression e is first linearized (linear.py); non-linear parts introduce
# temporary variables t, with constraints ("sides"), e.g. x // 2 becomes t
# with 2t <= x <= 2t + 1. The temporaries are added as extra dimensions, and
# projected away at the end.

def poly_fwd_assign(P, env, x, e):
    """ASSIGN_D[[x ← e]] P: the image of P by the assignment."""
    if P.empty:
        return P
    comp = compile_aexp(env, e)
    k = comp.ntemps
    if k:
        P = P.add_dimensions(k).meet_constraints((), comp.sides)
    P = P.assign(env.index[x], comp.expr)
    return P.remove_dimensions(k) if k else P


def poly_bwd_assign(P, env, x, e):
    """ASSIGN←_D[[x ← e]] P: the states from which the assignment can lead to P
    (pre-image), obtained by substituting e for x in the constraints of P."""
    if P.empty:
        return P
    comp = compile_aexp(env, e)
    k = comp.ntemps
    if k:
        P = P.add_dimensions(k)
    P = P.substitute(env.index[x], comp.expr)
    if k:
        P = P.meet_constraints((), comp.sides).remove_dimensions(k)
    return P


def poly_compare(P, env, b):
    """FILTER_D[[e1 ⋈ e2]] P: intersection with the constraint e1 ⋈ e2."""
    if P.empty:
        return P
    comp = compile_compare(env, b)
    k = comp.ntemps
    if k:
        P = P.add_dimensions(k)
    P = P.meet_constraints((), comp.sides + [comp.expr])
    return P.remove_dimensions(k) if k else P


def poly_str(P, names):
    if P.empty:
        return 'bottom'
    if P.is_universe():
        return 'top'
    out = []
    for e in P.eqs:
        out.append('%s == %s' % (linexpr_str(e[:-1], 0, names), -e[-1]))
    for c in P.ineqs:
        out.append(constraint_str(c, names))
    return ' && '.join(out)


class Partition:
    """Common interface of the numerical domains (cf. the PARTITION signature).
    The elements are immutable."""

    name = None

    def __init__(self, env):
        self.env = env

    def filter(self, b):
        """FILTER_D[[b]]: conjunctions are meets, disjunctions are joins."""
        if isinstance(b, (BConst, Maybe)):
            return self if (isinstance(b, Maybe) or b.value) else self.bot(self.env)
        if isinstance(b, Not):
            return self.filter(negate_bexp(b.expr))
        if isinstance(b, BoolOp):
            l = self.filter(b.left)
            r = self.filter(b.right)
            return l.meet(r) if b.op == 'and' else l.join(r)
        if isinstance(b, Compare):
            return self.from_poly(self.env, poly_compare(self.to_poly(), self.env, b))
        raise TypeError(b)

    def fwd_assign(self, x, e):
        if self.is_bot():
            return self
        return self.from_poly(self.env, poly_fwd_assign(self.to_poly(), self.env, x, e))

    def bwd_assign(self, x, e):
        if self.is_bot():
            return self
        return self.from_poly(self.env, poly_bwd_assign(self.to_poly(), self.env, x, e))

    def __str__(self):
        return poly_str(self.to_poly(), self.env.vars)

    _inner_cache = {}

    @classmethod
    def inner(cls, env, cs):
        """α_C(cs): the element of the domain described by a set of
        constraints (memoized, as the decision trees call it very often)."""
        key = (cls, id(env), frozenset(cs))
        r = Partition._inner_cache.get(key)
        if r is None:
            r = cls._inner(env, cs)
            Partition._inner_cache[key] = r
        return r

    @staticmethod
    def clear_caches():
        Partition._inner_cache.clear()


# intervals

def _fl(x):
    return None if x is None else floor(x)


def _cl(x):
    return None if x is None else ceil(x)


class Box(Partition):
    """Intervals: each variable is mapped to its lower and upper bounds."""

    name = 'boxes'
    __slots__ = ('env', 'b', '_poly')

    def __init__(self, env, b):
        self.env = env
        self.b = b  # None (bottom) or tuple of (lo, hi) pairs, None for infinity
        self._poly = None

    @classmethod
    def bot(cls, env):
        return cls(env, None)

    @classmethod
    def top(cls, env):
        return cls(env, ((None, None),) * env.n)

    @classmethod
    def _inner(cls, env, cs):
        b = [[None, None] for _ in range(env.n)]
        general = []
        for c in cs:
            nz = [i for i in range(env.n) if c[i] != 0]
            if not nz:
                if c[-1] < 0:
                    return cls.bot(env)
            elif len(nz) == 1:
                i = nz[0]
                a = c[i]
                if a > 0:  # x >= -c/a
                    lo = ceil(Fraction(-c[-1], a))
                    if b[i][0] is None or lo > b[i][0]:
                        b[i][0] = lo
                else:  # x <= c/-a
                    hi = floor(Fraction(c[-1], -a))
                    if b[i][1] is None or hi < b[i][1]:
                        b[i][1] = hi
            else:
                general.append(c)
        for lo, hi in b:
            if lo is not None and hi is not None and lo > hi:
                return cls.bot(env)
        box = cls(env, tuple(tuple(x) for x in b))
        if general:
            return cls.from_poly(env, box.to_poly().meet_constraints((), general))
        return box

    @classmethod
    def from_poly(cls, env, P):
        if P.empty:
            return cls.bot(env)
        b = []
        for i in range(env.n):
            lo, hi = P.bounds(tuple(1 if j == i else 0 for j in range(env.n + 1)))
            lo, hi = _cl(lo), _fl(hi)
            if lo is not None and hi is not None and lo > hi:
                return cls.bot(env)
            b.append((lo, hi))
        return cls(env, tuple(b))

    def constraints(self):
        if self.b is None:
            return [self.env.unsat()]
        n = self.env.n
        cs = []
        for i, (lo, hi) in enumerate(self.b):
            if lo is not None:
                cs.append(tuple(1 if j == i else 0 for j in range(n)) + (-lo,))
            if hi is not None:
                cs.append(tuple(-1 if j == i else 0 for j in range(n)) + (hi,))
        return cs

    def to_poly(self):
        if self._poly is None:
            if self.b is None:
                self._poly = Polyhedron.bottom(self.env.n)
            else:
                self._poly = Polyhedron.from_constraints(self.env.n, [], self.constraints())
        return self._poly

    def is_bot(self):
        return self.b is None

    def is_leq(self, other):
        if self.b is None:
            return True
        if other.b is None:
            return False
        for (l1, h1), (l2, h2) in zip(self.b, other.b):
            if l2 is not None and (l1 is None or l1 < l2):
                return False
            if h2 is not None and (h1 is None or h1 > h2):
                return False
        return True

    def join(self, other):
        if self.b is None:
            return other
        if other.b is None:
            return self
        b = []
        for (l1, h1), (l2, h2) in zip(self.b, other.b):
            lo = None if l1 is None or l2 is None else min(l1, l2)
            hi = None if h1 is None or h2 is None else max(h1, h2)
            b.append((lo, hi))
        return Box(self.env, tuple(b))

    def meet(self, other):
        if self.b is None:
            return self
        if other.b is None:
            return other
        b = []
        for (l1, h1), (l2, h2) in zip(self.b, other.b):
            lo = l2 if l1 is None else (l1 if l2 is None else max(l1, l2))
            hi = h2 if h1 is None else (h1 if h2 is None else min(h1, h2))
            if lo is not None and hi is not None and lo > hi:
                return Box.bot(self.env)
            b.append((lo, hi))
        return Box(self.env, tuple(b))

    def widen(self, other):
        """▿_D loosens the unstable bounds: [0, 1] ▿ [0, 2] = [0, +∞]."""
        if self.b is None:
            return other
        if other.b is None:
            return self
        b = []
        for (l1, h1), (l2, h2) in zip(self.b, other.b):
            lo = l1 if (l1 is not None and l2 is not None and l2 >= l1) else None
            hi = h1 if (h1 is not None and h2 is not None and h2 <= h1) else None
            b.append((lo, hi))
        return Box(self.env, tuple(b))

    def __str__(self):
        if self.b is None:
            return 'bottom'
        out = []
        for v, (lo, hi) in zip(self.env.vars, self.b):
            if lo is not None and lo == hi:
                out.append('%s == %s' % (v, lo))
            else:
                if lo is not None:
                    out.append('%s >= %s' % (v, lo))
                if hi is not None:
                    out.append('%s <= %s' % (v, hi))
        return ' && '.join(out) if out else 'top'


# octagons

_directions_cache = {}


def _directions(env):
    d = _directions_cache.get(id(env))
    if d is None:
        n = env.n
        d = []

        def unit(i, a):
            v = [0] * n
            v[i] = a
            return v

        for i in range(n):
            d.append(tuple(unit(i, 1)))
            d.append(tuple(unit(i, -1)))
        for i in range(n):
            for j in range(i + 1, n):
                for a in (1, -1):
                    for b in (1, -1):
                        v = [0] * n
                        v[i], v[j] = a, b
                        d.append(tuple(v))
        _directions_cache[id(env)] = d
    return d


_dbm_cache = {}


def _dbm_entries(env):
    """For each octagonal direction, the corresponding entry (row, column, unary)
    of the difference bound matrix over v_2i = x_i, v_2i+1 = -x_i."""
    e = _dbm_cache.get(id(env))
    if e is None:
        e = []
        for d in _directions(env):
            nz = [(i, a) for i, a in enumerate(d) if a]
            if len(nz) == 1:
                i, a = nz[0]
                p = 2 * i if a == 1 else 2 * i + 1
                e.append((p ^ 1, p, True))  # v_p - v_~p <= 2c
            else:
                (i, a), (j, b) = nz
                p = 2 * i if a == 1 else 2 * i + 1
                q = 2 * j + 1 if b == 1 else 2 * j
                e.append((q, p, False))  # v_p - v_q <= c
        _dbm_cache[id(env)] = (e, {d: k for k, d in enumerate(_directions(env))})
        e = _dbm_cache[id(env)]
    return e


_INF = float('inf')


def _close(env, b):
    """Tight closure (Bagnara, Hill & Zaffanella) of the octagon with direction
    bounds b; returns the closed bounds, or None if the octagon is empty."""
    # Difference bound matrix over v_2i = x_i, v_2i+1 = -x_i: m[r][c] bounds
    # v_c - v_r. The closure is Floyd-Warshall (shortest paths), followed by
    # the tightening of the unary bounds to even numbers (integer variables)
    # and by the strengthening m[i][j] <= (m[i][~i] + m[~j][j]) / 2.
    entries, _ = _dbm_entries(env)
    n2 = 2 * env.n
    m = [[_INF] * n2 for _ in range(n2)]
    for i in range(n2):
        m[i][i] = 0
    for (r, c, unary), k in zip(entries, b):
        if k is None:
            continue
        v = 2 * k if unary else k
        if v < m[r][c]:
            m[r][c] = v
            m[c ^ 1][r ^ 1] = v
    for k in range(n2):
        mk = m[k]
        for i in range(n2):
            mik = m[i][k]
            if mik == _INF:
                continue
            mi = m[i]
            for j in range(n2):
                v = mik + mk[j]
                if v < mi[j]:
                    mi[j] = v
    for i in range(n2):
        if m[i][i] < 0:
            return None
    for i in range(n2):
        v = m[i][i ^ 1]
        if v != _INF:
            m[i][i ^ 1] = 2 * (v // 2)
    for i in range(n2):
        if m[i][i ^ 1] + m[i ^ 1][i] < 0:
            return None
    for i in range(n2):
        mi = m[i]
        a = mi[i ^ 1]
        if a == _INF:
            continue
        for j in range(n2):
            v = m[j ^ 1][j]
            if v != _INF:
                w = (a + v) // 2
                if w < mi[j]:
                    mi[j] = w
    out = []
    for r, c, unary in entries:
        v = m[r][c]
        out.append(None if v == _INF else (v // 2 if unary else v))
    return tuple(out)


class Octagon(Partition):
    """Octagons, represented by the (tight) upper bounds of all octagonal
    directions ±x, ±x ± y, i.e., by a closed difference bound matrix.

    The join is the bound-wise maximum, the widening drops the unstable
    bounds; the meet and the conversion from constraints require a closure,
    to propagate the bounds (e.g. x - y <= 1 and y <= 2 imply x <= 3)."""

    name = 'octagons'
    __slots__ = ('env', 'b', '_poly')

    def __init__(self, env, b, poly=None):
        self.env = env
        self.b = b  # None (bottom) or tuple of upper bounds (None for infinity)
        self._poly = poly

    @classmethod
    def bot(cls, env):
        return cls(env, None)

    @classmethod
    def top(cls, env):
        return cls(env, (None,) * len(_directions(env)))

    @classmethod
    def _inner(cls, env, cs):
        _, index = _dbm_entries(env)
        b = [None] * len(index)
        general = []
        for c in cs:
            a = tuple(-x for x in c[:-1])  # a.x <= c[-1]
            nz = [x for x in a if x]
            if not nz:
                if c[-1] < 0:
                    return cls.bot(env)
                continue
            k = abs(nz[0])
            if len(nz) > 2 or any(abs(x) != k for x in nz):
                general.append(c)
                continue
            d = tuple(x // k for x in a)
            v = floor(Fraction(c[-1], k))
            i = index[d]
            if b[i] is None or v < b[i]:
                b[i] = v
        o = cls._from_bounds(env, tuple(b))
        if general and not o.is_bot():
            return cls.from_poly(env, o.to_poly().meet_constraints((), general))
        return o

    @classmethod
    def from_poly(cls, env, P):
        if P.empty:
            return cls.bot(env)
        b = tuple(_fl(P.bounds(d + (0,))[1]) for d in _directions(env))
        return cls._from_bounds(env, b)

    @classmethod
    def _from_bounds(cls, env, b):
        b = _close(env, b)
        return cls.bot(env) if b is None else cls(env, b)

    def constraints(self):
        if self.b is None:
            return [self.env.unsat()]
        return [tuple(-x for x in d) + (k,) for d, k in zip(_directions(self.env), self.b) if k is not None]

    def to_poly(self):
        if self._poly is None:
            if self.b is None:
                self._poly = Polyhedron.bottom(self.env.n)
            else:
                self._poly = Polyhedron.from_constraints(self.env.n, [], self.constraints())
        return self._poly

    def is_bot(self):
        return self.b is None

    def is_leq(self, other):
        if self.b is None:
            return True
        if other.b is None:
            return False
        return all(k2 is None or (k1 is not None and k1 <= k2) for k1, k2 in zip(self.b, other.b))

    def join(self, other):
        if self.b is None:
            return other
        if other.b is None:
            return self
        return Octagon(self.env, tuple(None if k1 is None or k2 is None else max(k1, k2)
                                       for k1, k2 in zip(self.b, other.b)))

    def meet(self, other):
        if self.b is None:
            return self
        if other.b is None:
            return other
        b = tuple(k2 if k1 is None else (k1 if k2 is None else min(k1, k2)) for k1, k2 in zip(self.b, other.b))
        return Octagon._from_bounds(self.env, b)

    def widen(self, other):
        """▿_D drops the unstable bounds. The result is deliberately not
        closed: closing the widened iterates could prevent convergence."""
        if self.b is None:
            return other
        if other.b is None:
            return self
        return Octagon(self.env, tuple(k1 if (k1 is not None and k2 is not None and k2 <= k1) else None
                                       for k1, k2 in zip(self.b, other.b)))


# polyhedra

def _tighten_poly(n, P):
    if P.empty:
        return P
    for e in P.eqs:
        g = 0
        for x in e[:-1]:
            g = gcd(g, x)
        if g > 1 and e[-1] % g != 0:
            return Polyhedron.bottom(n)
    ineqs = [tighten(c) for c in P.ineqs]
    if ineqs != P.ineqs:
        return Polyhedron.from_constraints(n, P.eqs, ineqs)
    return P


class Polyhedra(Partition):
    """Convex polyhedra: ⊑_D is inclusion, ⊔_D the convex hull,
    ⊓_D the intersection, ▿_D removes the unstable constraints."""

    name = 'polyhedra'
    __slots__ = ('env', 'p')

    def __init__(self, env, p):
        self.env = env
        self.p = p

    @classmethod
    def bot(cls, env):
        return cls(env, Polyhedron.bottom(env.n))

    @classmethod
    def top(cls, env):
        return cls(env, Polyhedron.universe(env.n))

    @classmethod
    def _inner(cls, env, cs):
        return cls.from_poly(env, Polyhedron.from_constraints(env.n, [], [tighten(c) for c in cs]))

    @classmethod
    def from_poly(cls, env, P):
        return cls(env, _tighten_poly(env.n, P))

    def constraints(self):
        if self.p.empty:
            return [self.env.unsat()]
        return [tighten(c) for c in self.p.constraint_list()]

    def to_poly(self):
        return self.p

    def is_bot(self):
        return self.p.empty

    def is_leq(self, other):
        return self.p.is_leq(other.p)

    def join(self, other):
        return Polyhedra.from_poly(self.env, self.p.join(other.p))

    def meet(self, other):
        return Polyhedra.from_poly(self.env, self.p.meet(other.p))

    def widen(self, other):
        return Polyhedra(self.env, self.p.widen(other.p))


DOMAINS = {'boxes': Box, 'octagons': Octagon, 'polyhedra': Polyhedra}
