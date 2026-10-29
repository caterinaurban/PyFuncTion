"""
The functions auxiliary abstract domain F, for the leaves of the decision trees:

  - Affine: natural-valued affine ranking functions (cf. domains/Affines.ml)

        F_A = {⊥_F} ∪ { λX1,...,Xk. m1*X1 + ... + mk*Xk + q } ∪ {⊤_F}

  - Ordinals: ordinal-valued ranking functions in Cantor normal form, whose
    coefficients are affine functions (cf. domains/Ordinals.ml)

        W = {⊥_W} ∪ { Σ_i ω^i * f_i } ∪ {⊤_W}

Both ⊥_F and ⊤_F denote undefined functions (γ_F = ∅), but with different
meanings: ⊥_F means "termination not (yet) established", while ⊤_F means
"undefined because of a loss of precision" (e.g. after a widening or a
non-linear assignment). They are ordered differently by the two orders:

  - approximation order ≼_F: ⊥_F and ⊤_F are both above the
    defined functions (a ranking function with a smaller domain is larger),
    and ⊥_F ≼_F ⊤_F; it is the order of the ranking functions;
  - computational order ⊑_F: ⊥_F is the least element and ⊤_F the
    greatest one; it is used to compute the fixpoints.

Each operator is relative to a partition b of the decision tree, an element of
the numerical domain D (written [D], e.g. f1 ≼_F[D] f2): the
functions are only compared or combined on the states in γ_D(b). The `kind`
argument is APPROXIMATION or COMPUTATIONAL (cf. domains/Functions.ml).
"""

from fractions import Fraction

from .polyhedra import Polyhedron, dot
from .linear import compile_aexp, integer_vector, linexpr_str

APPROXIMATION = 'approximation'
COMPUTATIONAL = 'computational'

BOT, FUN, TOP = 0, 1, 2


class Aff:
    """An element of F_A: an affine function sum coeffs[i]*x_i + const (kind
    FUN, with rational coefficients), ⊥_F (kind BOT) or ⊤_F (kind TOP)."""

    __slots__ = ('kind', 'coeffs', 'const')

    def __init__(self, kind, coeffs=None, const=Fraction(0)):
        self.kind = kind
        self.coeffs = coeffs
        self.const = const

    def __eq__(self, other):
        return (isinstance(other, Aff) and self.kind == other.kind
                and self.coeffs == other.coeffs and self.const == other.const)

    def __hash__(self):
        return hash((self.kind, self.coeffs, self.const))


def _sign_on(P, coeffs, const):
    """Returns (nonneg, zero): whether the affine function is >= 0 / = 0 over P.

    An affine function is >= 0 on a polyhedron iff it is >= 0 on its vertices,
    non-decreasing along its rays, and constant along its lines: it suffices
    to look at the generators of P (see polyhedra.py)."""
    zero = True
    for l in P.lines:
        if dot(coeffs, l) != 0:
            return False, False
    for r in P.rays:
        s = dot(coeffs, r) + const * r[-1]
        if s < 0:
            return False, False
        if s != 0:
            zero = False
    return True, zero


class Affine:
    """The affine functions abstract domain (parameterized by the environment)."""

    def __init__(self, env):
        self.env = env
        self.n = env.n
        self._zero = Aff(FUN, (Fraction(0),) * env.n, Fraction(0))
        self._bot = Aff(BOT)
        self._top = Aff(TOP)

    def bot(self):
        return self._bot

    def zero(self):
        return self._zero

    def top(self):
        return self._top

    @staticmethod
    def is_bot(f):
        return f.kind == BOT

    @staticmethod
    def defined(f):
        return f.kind == FUN

    @staticmethod
    def is_top(f):
        return f.kind == TOP

    # helpers

    def _diff(self, f1, f2):
        return tuple(a - b for a, b in zip(f1.coeffs, f2.coeffs)), f1.const - f2.const

    def _hypograph(self, b, f):
        """{ (x, #) | x in b, # <= f(x) } as a polyhedron over the variables and #.

        Most operators on affine functions are implemented with polyhedra
        over the program variables and an extra dimension # for the value of
        the function: an affine function f on a partition b is represented by
        its hypograph, and e.g. the join of two functions is read off the
        convex hull of their hypographs."""
        vec, _ = integer_vector(f.coeffs + (Fraction(-1),), f.const)
        return b.to_poly().add_dimensions(1).meet_constraints((), [vec])

    def _reduce(self, eqs, f):
        """Canonical form of f modulo the equalities eqs (integer vectors whose
        first n entries are the coefficients of the program variables and whose
        last entry is the constant): as in NewPolka, the equalities are put in
        reduced echelon form and their pivots (the first variable with a
        non-zero coefficient) are eliminated from f."""
        n = self.n
        if f.kind != FUN or not eqs:
            return f
        rows = []  # (pivot, coefficients, constant)
        for e in eqs:
            r = [Fraction(x) for x in e[:n]]
            c = Fraction(e[-1])
            for p, rr, rc in rows:
                if r[p]:
                    k = r[p] / rr[p]
                    r = [x - k * y for x, y in zip(r, rr)]
                    c -= k * rc
            piv = next((i for i, x in enumerate(r) if x), None)
            if piv is None:
                continue
            nrows = []
            for p, rr, rc in rows:
                if rr[piv]:
                    k = rr[piv] / r[piv]
                    rr = [x - k * y for x, y in zip(rr, r)]
                    rc -= k * c
                nrows.append((p, rr, rc))
            rows = nrows + [(piv, r, c)]
        coeffs = list(f.coeffs)
        const = f.const
        for p, rr, rc in rows:
            if coeffs[p]:
                k = coeffs[p] / rr[p]
                coeffs = [x - k * y for x, y in zip(coeffs, rr)]
                const -= k * rc
        return Aff(FUN, tuple(coeffs), const)

    def _ranking_constraints(self, P):
        """The constraints of P mentioning #, as affine functions (None if # is
        not bounded from above by some of them): a constraint
        a.x - k*# + q >= 0 with k > 0 is the upper bound # <= (a.x + q)/k."""
        n = self.n
        res = []
        if P.empty:
            return res, 0
        total = len(P.eqs) + len(P.ineqs)
        eqs = []
        for e in P.eqs:
            if e[n] != 0:
                res.append(None)
            else:
                eqs.append(e[:n] + e[n + 1:])
        for c in P.ineqs:
            if c[n] < 0:
                k = Fraction(-c[n])
                f = Aff(FUN, tuple(Fraction(x) / k for x in c[:n]), Fraction(c[n + 1]) / k)
                res.append(self._reduce(eqs, f))
            elif c[n] > 0:
                res.append(None)
        return res, total

    # orderings

    def is_eq(self, b, f1, f2):
        """f1 = f2 on the partition b."""
        if f1.kind == FUN and f2.kind == FUN:
            if f1 == f2:
                return True
            coeffs, const = self._diff(f1, f2)
            return _sign_on(b.to_poly(), coeffs, const)[1]
        return f1.kind == f2.kind

    def domain_eq(self, b, f1, f2):
        """The part of b where f1 = f2 (used by the ordinals)."""
        if f1.kind == FUN and f2.kind == FUN:
            coeffs, const = self._diff(f1, f2)
            vec, _ = integer_vector(coeffs, const)
            return type(b).from_poly(b.env, b.to_poly().meet_constraints([vec], ()))
        if f1.kind == f2.kind:
            return b
        return type(b).bot(b.env)

    def _leq(self, b, f1, f2):
        coeffs, const = self._diff(f2, f1)
        return _sign_on(b.to_poly(), coeffs, const)[0]

    def is_leq(self, k, b, f1, f2):
        """f1 ≼_F[b] f2 (k = APPROXIMATION) or f1 ⊑_F[b] f2 (k = COMPUTATIONAL).
        Between defined functions: ∀ρ ∈ γ_D(b): f1(ρ) <= f2(ρ)."""
        if f1.kind == FUN and f2.kind == FUN:
            return f1 == f2 or self._leq(b, f1, f2)
        # otherwise, the orders between ⊥_F, ⊤_F and the defined functions
        # described at the top of the module
        if f1.kind == BOT and f2.kind == FUN:
            return k == COMPUTATIONAL
        if f1.kind == FUN and f2.kind == BOT:
            return k == APPROXIMATION
        return f1.kind == BOT or f2.kind == TOP

    # binary operators

    def join(self, k, b, f1, f2):
        """f1 ⋎_F[b] f2 (k = APPROXIMATION) or f1 ⊔_F[b] f2 (k = COMPUTATIONAL).

        Between defined functions, the join is λρ ∈ γ_D(b). max(f1(ρ), f2(ρ))
        if this is an affine function, ⊤_F otherwise. In practice, the convex
        hull of the hypographs gives the smallest affine upper bound of
        max(f1, f2) on b, when there is a unique one. Undefined functions:
        ⊥_F ⋎_F f = ⊥_F but ⊥_F ⊔_F f = f; ⊤_F absorbs everything else."""
        if f1.kind == FUN and f2.kind == FUN:
            if b.is_bot():
                return self._top
            # shortcuts: when one function dominates the other on b, it is the max
            if f1 == f2 or self._leq(b, f2, f1):
                return self._reduce(b.to_poly().eqs, f1)
            if self._leq(b, f1, f2):
                return self._reduce(b.to_poly().eqs, f2)
            P = self._hypograph(b, f1).join(self._hypograph(b, f2))
            fs, _ = self._ranking_constraints(P)
            if len(fs) == 1 and fs[0] is not None:
                return fs[0]
            return self._top
        if f1.kind == BOT:
            return self._bot if k == APPROXIMATION else f2
        if f2.kind == BOT:
            return self._bot if k == APPROXIMATION else f1
        return self._top

    def widen(self, b, f1, f2, jokers=0):
        """f1 ▿_F[b] f2: the polyhedra widening of the hypographs (constraints
        of f1 that are not stable are dropped); ⊤_F if the result is not
        bounded by a single affine function.

        While jokers > 0, the widening is postponed and f2 is returned (unless
        one of the functions is ⊤_F), exactly as for the ordinal-valued
        functions with no power of ω (Ordinals.widen with max = 0): this
        makes -ordinals 0 equivalent to no ordinals. Unlike FuncTion, where
        the affine widening ignores the jokers."""
        if jokers > 0 and f1.kind != TOP and f2.kind != TOP:
            return f2
        if f1.kind == FUN and f2.kind == FUN:
            if b.is_bot():
                return self._top
            if f1 == f2:
                return self._reduce(b.to_poly().eqs, f1)
            P = self._hypograph(b, f1).widen(self._hypograph(b, f2))
            fs, _ = self._ranking_constraints(P)
            if len(fs) == 1 and fs[0] is not None:
                return fs[0]
            return self._top
        if f1.kind == BOT:
            return f2
        if f2.kind == BOT:
            return f1
        return self._top

    def extend(self, b1, b2, f1, f2):
        """The extrapolation operator ▾_F[b1, b2](f1, f2) of the value widening:
        f2, defined on the partition b2, is extended using its
        adjacent leaf f1, defined on b1. The hull of the two hypographs gives
        candidate affine functions that bound both pieces; they are joined on
        b2. E.g. f1 = 3 on x = 1 and f2 = 5 on x = 2 extrapolate to 2x + 1."""
        if f1.kind == FUN and f2.kind == FUN:
            P = self._hypograph(b1, f1).join(self._hypograph(b2, f2))
            fs, _ = self._ranking_constraints(P)
            fs = [f for f in fs if f is not None]
            if not fs:
                return self._top
            r = fs[0]
            for f in fs[1:]:
                r = self.join(COMPUTATIONAL, b2, r, f)
            return r
        return f2

    # unary operators

    def reset(self, f):
        return self._zero

    @staticmethod
    def predecessor(f):
        """f - 1 (used by the ordinals)"""
        if f.kind == FUN:
            return Aff(FUN, f.coeffs, f.const - 1)
        return f

    @staticmethod
    def successor(f):
        """STEP_F(f) = λX1,...,Xk. f(X1,...,Xk) + 1 on defined functions."""
        if f.kind == FUN:
            return Aff(FUN, f.coeffs, f.const + 1)
        return f

    def bwd_assign(self, f, x, e):
        """ASSIGN←_F[[X ← e]](f): the maximum of f(..., v, ...) + 1
        over the possible values v of e, or ⊤_F if it is not affine.

        For a deterministic linear expression, this is just the substitution
        f[X := e] + 1. With non-determinism, e.g. X ← X + [1, 2] and
        f = λx. x + 1, we get max{x + v + 1 + 1 | v ∈ [1, 2]} = x + 4."""
        if f.kind != FUN:
            return f
        n = self.n
        i = self.env.index[x]
        comp = compile_aexp(self.env, e)
        a = f.coeffs[i]
        if comp.ntemps == 0:
            # deterministic linear expression: substitution, plus one step
            if a == 0:
                return Aff(FUN, f.coeffs, f.const + 1)
            ex = comp.expr
            coeffs = tuple((c if j != i else 0) + a * ex[j] for j, c in enumerate(f.coeffs))
            return Aff(FUN, coeffs, f.const + a * ex[n] + 1)
        # the expression introduces temporaries (non-determinism, // or %):
        # substitute in the hypograph # <= f, constrain the temporaries, and
        # project them away; the maximum is the upper bound left on #
        k = comp.ntemps

        def ins(v):  # insert the # dimension after the program variables
            return v[:n] + (0,) + v[n:]

        vec, _ = integer_vector(f.coeffs + (Fraction(-1),), f.const)
        P = Polyhedron.from_constraints(n + 1, [], [vec]).add_dimensions(k)
        P = P.substitute(i, ins(comp.expr))
        P = P.meet_constraints((), [ins(s) for s in comp.sides]).remove_dimensions(k)
        fs, total = self._ranking_constraints(P)
        if total == 1 and len(fs) == 1 and fs[0] is not None:
            return self.successor(fs[0])
        return self._top

    def bwd_assign_angelic(self, f, x, e, Q, b, unit):
        """The value of a leaf for an angelic choice X ← e (option -angelic,
        see DecisionTree.bwd_assign_angelic), on the partition b before the
        assignment, where Q = { (ρ, v) | v ∈ e(ρ), ρ[X := v] is in the
        partition of f } (a polyhedron over the variables and v):

            inf { f(ρ[X := v]) | ρ ∈ γ_D(b), (ρ, v) ∈ Q } + 1

        the number of steps when the program picks its best value v. The
        inf is computed over the rationals: it is reached at a bound of v,
        an integer when all the bounds on v have coefficient ±1 (`unit`);
        otherwise, or when the inf is not affine on b, the sup is used
        instead, which is sound but coarser (e.g. f = x + 1 on x <= 5 with
        X ← ? gives 7: the sup is only over the values that stay in the
        partition of f, unlike in the VMCAI 2026 paper).
        (Difference (d) in DecisionTree.bwd_assign_angelic.)"""
        if f.kind != FUN:
            return f
        n = self.n
        i = self.env.index[x]
        # f(ρ[X := v]) - # >= 0, over the variables, #, and v
        vec, _ = integer_vector(tuple(c if j != i else 0 for j, c in enumerate(f.coeffs))
                                + (Fraction(-1), f.coeffs[i]), f.const)
        qs = [c[:n] + (0,) + c[n:] for c in Q.ineqs]
        qe = [c[:n] + (0,) + c[n:] for c in Q.eqs]
        bs = [c[:n] + (0, 0) + c[n:] for c in b.to_poly().constraint_list()]
        if unit:
            # epigraph # >= f(ρ[X := v]), v projected away: the lower bounds
            # left on # are the inf (their maximum)
            neg = tuple(-a for a in vec)
            P = Polyhedron.from_constraints(n + 2, qe, qs + bs + [neg]).remove_dimensions(1)
            gs = []
            for c in P.ineqs:
                if c[n] > 0:
                    k = Fraction(c[n])
                    gs.append(self._reduce(P.eqs, Aff(FUN, tuple(-Fraction(a) / k for a in c[:n]),
                                                      -Fraction(c[n + 1]) / k)))
            if gs:
                g = gs[0]
                for h in gs[1:]:
                    g = self.join(COMPUTATIONAL, b, g, h)
                if g.kind == FUN:
                    return self.successor(g)
        # hypograph # <= f(ρ[X := v]): each upper bound left on # bounds the
        # sup (which is their minimum)
        P = Polyhedron.from_constraints(n + 2, qe, qs + bs + [vec]).remove_dimensions(1)
        fs = [g for g in self._ranking_constraints(P)[0] if g is not None]
        return self.successor(fs[0]) if fs else self._top

    def filter(self, f, b):
        """A test is one execution step: STEP_F."""
        return self.successor(f)

    def to_str(self, f):
        if f.kind == BOT:
            return 'bottom'
        if f.kind == TOP:
            return 'top'
        return linexpr_str(f.coeffs, f.const, self.env.vars)


class Ord:
    """An ordinal-valued function in Cantor normal form:

        ... + ω^2 * ff[1] + ω * ff[0] + f

    where f and the coefficients ff[i] are affine functions. E.g. the ranking
    function ω*(x1 - 7) + 7*x1 + 3*x2 - 5 is
    Ord(7*x1 + 3*x2 - 5, [x1 - 7])."""

    __slots__ = ('f', 'ff')

    def __init__(self, f, ff=()):
        self.f = f
        self.ff = tuple(ff)


class Ordinals:
    """Ordinal-valued ranking functions W, parameterized by a function domain
    F for the coefficients (cf. domains/Ordinals.ml).

    Ordinals are needed when no natural-valued bound exists, e.g. when a loop
    counter is reset to an arbitrary value: after x ← [-∞, +∞]
    the number of steps is unbounded, but finite. The operators work "in
    ascending powers of ω": the operator of F is applied to
    the coefficient of ω^0, then of ω^1, ..., and when a coefficient becomes
    undefined, it is replaced by 0 and 1 is carried to the next power of ω
    (as in ω*ω = ω^2*1 + ω*0). `max` bounds the powers of ω (option -ordinals)."""

    def __init__(self, F, max_ordinal):
        self.F = F
        self.env = F.env
        self.max = max_ordinal

    def bot(self):
        return Ord(self.F.bot())

    def zero(self):
        return Ord(self.F.zero())

    def top(self):
        return Ord(self.F.top())

    def is_bot(self, o):
        return self.F.is_bot(o.f)

    def defined(self, o):
        return self.F.defined(o.f)

    def is_top(self, o):
        return self.F.is_top(o.f)

    def is_eq(self, b, o1, o2):
        F = self.F
        if not F.is_eq(b, o1.f, o2.f):
            return False
        ff1, ff2 = list(o1.ff), list(o2.ff)
        while ff1 or ff2:
            x = ff1.pop(0) if ff1 else F.zero()
            y = ff2.pop(0) if ff2 else F.zero()
            if not F.is_eq(b, x, y):
                return False
        return True

    def domain_eq(self, b, o1, o2):
        F = self.F
        r = F.domain_eq(b, o1.f, o2.f)
        ff1, ff2 = list(o1.ff), list(o2.ff)
        while ff1 or ff2:
            x = ff1.pop(0) if ff1 else F.zero()
            y = ff2.pop(0) if ff2 else F.zero()
            r = F.domain_eq(r, x, y)
        return r

    def is_leq(self, k, b, o1, o2):
        """Lexicographic comparison of the coefficients, from the highest
        power of ω down to ω^0: o1 <= o2 on b if, on the
        part of b where the higher coefficients are equal, the next
        coefficient of o1 is smaller."""
        F = self.F

        def aux(ff1, ff2):
            # returns the domain on which ff1 and ff2 are equal,
            # or None if there is a point where ff1 > ff2
            if not ff1 and not ff2:
                return b
            x = ff1[0] if ff1 else F.zero()
            y = ff2[0] if ff2 else F.zero()
            r = aux(ff1[1:], ff2[1:])
            if r is None:
                return None
            if F.is_leq(k, r, x, y):
                return F.domain_eq(r, x, y)
            return None

        if F.defined(o1.f) and F.defined(o2.f):
            r = aux(o1.ff, o2.ff)
            if r is None:
                return False
            return F.is_leq(k, r, o1.f, o2.f)
        return F.is_leq(k, b, o1.f, o2.f)

    def _carry(self, k, b, ff1, ff2, i):
        """Joins the coefficients of the powers of ω, in ascending powers of ω,
        propagating carries: a coefficient whose join is undefined becomes 0
        and adds 1 to the next power (i is the incoming carry)."""
        F = self.F
        out = []
        ff1, ff2 = list(ff1), list(ff2)
        while True:
            if not ff1 and not ff2:
                if i:
                    out.append(F.successor(F.zero()))
                return out
            if not ff1:
                x = F.zero()
                y = ff2.pop(0)
                z = F.join(k, b, x, y)
                fallback = x
            elif not ff2:
                x = ff1.pop(0)
                y = F.zero()
                z = F.join(k, b, x, y)
                fallback = y
            else:
                x = ff1.pop(0)
                y = ff2.pop(0)
                z = F.join(k, b, x, y)
                fallback = F.zero()
            if F.defined(z):
                out.append(F.successor(z) if i else z)
                i = 0
            else:
                out.append(F.successor(fallback) if i else fallback)
                i = 1

    def join(self, k, b, o1, o2):
        """The approximation/computational join in ascending powers of ω.
        Example:
            (ω^2*x1 + ω*x2 + 3) ⋎ (ω^2*x1 + ω*(-x2) + 4) = ω^2*(x1 + 1) + ω*0 + 4
        since x2 and -x2 have no affine upper bound: the coefficient of ω
        becomes 0, with a carry of 1 to the coefficient of ω^2."""
        F = self.F
        f = F.join(k, b, o1.f, o2.f)  # coefficient of ω^0
        if F.defined(f):
            ff = self._carry(k, b, o1.ff, o2.ff, 0)
            if len(ff) > self.max:
                return Ord(F.top())
            return Ord(f, ff)
        if F.is_bot(f):
            return Ord(f)
        if F.defined(o1.f) and F.defined(o2.f):
            # the coefficient of ω^0 has no affine bound: 0, and carry 1 to ω
            ff = self._carry(k, b, o1.ff, o2.ff, 1)
            if len(ff) > self.max:
                return Ord(f)
            return Ord(F.zero(), ff)
        return Ord(f)

    def widen(self, b, o1, o2, jokers=0):
        """Widening in ascending powers of ω: when the widening of
        a coefficient yields ⊤_F, the coefficient becomes 0 and 1 is carried
        to the next power of ω; the result is ⊤_W beyond ω^max.

        The jokers (see termination.TerminationAnalysis._bwd_while) postpone
        the widening of the coefficients: only the i = max + 1 - jokers
        lowest powers of ω are widened, the others simply take the new value."""
        F = self.F

        def succ(ff):  # adds 1 to the coefficient of ω
            if not ff:
                return [F.successor(F.zero())]
            return [F.successor(ff[0])] + list(ff[1:])

        def aux(i, ff1, ff2):
            ff1, ff2 = list(ff1), list(ff2)
            if not ff1 and not ff2:
                return []
            if not ff1:
                return aux(i, ff2, ff2)
            if not ff2:
                return aux(i, ff1, ff1)
            x, xs = ff1[0], ff1[1:]
            y, ys = ff2[0], ff2[1:]
            z = F.widen(b, x, y) if i > 0 else y
            if F.is_top(z):
                return [F.zero()] + aux(i - 1, xs, succ(ys))
            return [z] + aux(i - 1, xs, ys)

        i = self.max + 1 - jokers
        if F.is_top(o1.f) or F.is_top(o2.f):
            return Ord(F.widen(b, o1.f, o2.f))
        f = F.widen(b, o1.f, o2.f) if i > 0 else o2.f
        if F.is_top(f):
            ff = aux(i - 1, o1.ff, succ(o2.ff))
            if len(ff) > self.max:
                return self.top()
            return Ord(F.zero(), ff)
        if F.defined(f):
            ff = aux(i - 1, o1.ff, o2.ff)
            if len(ff) > self.max:
                return self.top()
            return Ord(f, ff)
        return Ord(f)

    def extend(self, b1, b2, o1, o2):
        """The extrapolation ▾_F applied to each coefficient."""
        F = self.F
        f = F.extend(b1, b2, o1.f, o2.f)
        if F.defined(f):
            ff1, ff2 = list(o1.ff), list(o2.ff)
            ff = []
            while ff1 or ff2:
                x = ff1.pop(0) if ff1 else F.zero()
                y = ff2.pop(0) if ff2 else F.zero()
                ff.append(F.extend(b1, b2, x, y))
            if any(F.is_top(x) for x in ff):
                return Ord(F.top())
            return Ord(f, ff)
        return Ord(f)

    def reset(self, o):
        return Ord(self.F.reset(o.f))

    def predecessor(self, o):
        return Ord(self.F.predecessor(o.f), o.ff)

    def successor(self, o):
        return Ord(self.F.successor(o.f), o.ff)

    def bwd_assign(self, o, x, e):
        """ASSIGN←_W in ascending powers of ω. Example:
            ASSIGN←_W[[x1 ← [-∞, +∞]]](ω*x1 + x2) = ω^2*1 + ω*0 + x2 + 1
        since the coefficient x1 of ω becomes unbounded: it is replaced by
        0, with a carry of 1 to ω^2 (ω*ω = ω^2*1 + ω*0)."""
        F = self.F

        def aux(i, ff):
            # the coefficients of the powers of ω > 0 (STEP_F is only
            # applied to the coefficient of ω^0, hence the predecessor)
            out = []
            for y in ff:
                y = F.predecessor(F.bwd_assign(y, x, e))
                if F.defined(y):
                    out.append(F.successor(y) if i else y)
                    i = 0
                else:
                    out.append(F.successor(F.zero()) if i else F.zero())
                    i = 1
            if i:
                out.append(F.successor(F.zero()))
            return out

        if F.defined(o.f):
            f = F.bwd_assign(o.f, x, e)
            if F.defined(f):
                ff = aux(0, o.ff)
                if len(ff) > self.max:
                    return Ord(F.top())
                return Ord(f, ff)
            if F.is_bot(f):
                return Ord(f)
            ff = aux(1, o.ff)
            if len(ff) > self.max:
                return Ord(f)
            return Ord(F.zero(), ff)
        return Ord(o.f)

    def bwd_assign_angelic(self, o, x, e, Q, b, unit):
        """The leaf value for an angelic choice (option -angelic). The
        ordinals are compared from the highest power of ω: when none of the
        coefficients of the powers of ω > 0 depends on X, the choice only
        changes the coefficient of ω^0, and the best value of the program is
        the one that minimizes it (F.bwd_assign_angelic); the other
        coefficients are unchanged, as in ASSIGN←_W. Otherwise, the sup over
        the whole range of e (ASSIGN←_W, as in the VMCAI 2026 paper), which is
        sound but coarser."""
        F = self.F
        i = self.env.index[x]
        if F.defined(o.f) and all(F.defined(y) and y.coeffs[i] == 0 for y in o.ff):
            f = F.bwd_assign_angelic(o.f, x, e, Q, b, unit)
            if F.defined(f):
                return Ord(f, o.ff)
        return self.bwd_assign(o, x, e)

    def filter(self, o, b):
        """STEP_W: one more step, added to the coefficient of ω^0."""
        return Ord(self.F.filter(o.f, b), o.ff)

    def to_str(self, o):
        F = self.F
        s = ''
        for i in range(len(o.ff), 0, -1):
            w = 'ω' if i == 1 else 'ω^%d' % i
            s += '(%s)%s + ' % (F.to_str(o.ff[i - 1]), w)
        return s + F.to_str(o.f)

