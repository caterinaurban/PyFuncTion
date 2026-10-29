"""
Forward/backward termination analysis (cf. main/TerminationIterator.ml).

The analysis proceeds in three steps:

  1. a FORWARD analysis computes an over-approximation R♮ of the reachable
     states at each program label (abstract forward reachability semantics),
     using the numerical domain D (boxes, octagons or polyhedra);

  2. a BACKWARD analysis computes the abstract definite termination semantics
     R#_M: at each label, a piecewise-defined ranking function, represented
     by a decision tree t ∈ A, that over-approximates the number of steps to
     termination;

  3. the program definitely terminates for all the initial states I in the
     precondition if I ⊆ dom(γ_A(R#_M[[s]])) (soundness corollary),
     i.e., if the ranking function at the program entry is defined on I.

Throughout, `p` denotes an abstract element: an element of D in the forward
analysis, a decision tree in the backward analysis.
"""

import sys
import time

from .syntax import Assign, Assume, If, While, Return, BConst, Not, BoolOp, Compare, negate
from .linear import Env, tighten, negate as negate_constraint, compile_compare
from .partition import DOMAINS, Partition
from .functions import Affine, Ordinals, APPROXIMATION, COMPUTATIONAL
from .decision_tree import DecisionTree


class Timeout(Exception):
    pass


def seed_constraints(env, seeds):
    """The linear constraints (in canonical form) of the seeds, conditions
    over the program variables: each comparison in them is a seed, e.g.
    'x == 0' gives x >= 0 and -x >= 0, 'x >= 0 and x - y >= 1' gives two
    seeds. A seed and its negation are the same seed."""
    out = {}

    def atoms(b):
        if isinstance(b, BoolOp):
            atoms(b.left)
            atoms(b.right)
        elif isinstance(b, Not):
            atoms(b.expr)
        elif isinstance(b, Compare):
            comp = compile_compare(env, b)
            if comp.ntemps:
                raise ValueError('the seeds must be linear constraints')
            c = tighten(comp.expr)
            nc = negate_constraint(c)
            if any(c[:-1]):  # (constant comparisons are no seeds)
                out.setdefault(max(c, nc), c)
        elif not isinstance(b, BConst):
            raise ValueError('unsupported seed')

    for b in seeds:
        atoms(b)
    return list(out.values())


class TerminationAnalysis:
    """The analyzer, parameterized by the abstract domains:

      - B: the numerical domain D used for the partitions of the decision
        trees, and for the forward analysis (boxes, octagons, polyhedra);
      - F: the functions at the leaves of the decision trees: affine
        functions (natural-valued ranking functions), possibly
        lifted to ordinals (ordinal-valued ranking functions);
      - D: the piecewise-defined ranking functions A (decision trees), built
        on top of B and F.
    """

    def __init__(self, program, domain='boxes', ordinals=None, joinfwd=2, joinbwd=2,
                 refine=False, retrybwd=5, timeout=300.0, tracefwd=False, tracebwd=False,
                 out=sys.stdout, record=None, seeds=()):
        if domain not in DOMAINS:
            raise ValueError('unknown abstract domain %s' % domain)
        self.program = program
        self.env = Env(program.variables)
        self.B = DOMAINS[domain]
        F = Affine(self.env)
        if ordinals is not None:
            F = Ordinals(F, ordinals)
        # affine functions are ordinal-valued functions with no power of ω:
        # without -ordinals, the jokers are computed as for -ordinals 0 (and
        # Affine.widen honours them), so that the two are equivalent
        self.ordmax = ordinals if ordinals is not None else 0
        self.out = out
        self.D = DecisionTree(self.B, F, self.env, retrybwd, self._trace if tracebwd else None)
        self.joinfwd = joinfwd    # widening delay of the forward analysis
        self.joinbwd = joinbwd    # widening delay of the backward analysis
        self.refine = refine      # restrict the backward analysis to the reachable states R♮
        self.seeds = seed_constraints(self.env, seeds)  # the decision trees start split on them
        self.retrybwd = retrybwd  # see the jokers in _bwd_while
        self.timeout = timeout
        self.tracefwd = tracefwd
        self.tracebwd = tracebwd
        # record(kind, label, tree, **info): called at each step of the
        # backward analysis, e.g. to replay it step by step (see web.py)
        self.record = record
        if record is not None:
            self.D.record = lambda kind, t: record(kind, None, t)
        self.fwd = {}  # label -> element of D (the forward invariants R♮)
        self.bwd = {}  # label -> decision tree (the ranking functions R#_M)
        self.start = 0.0

    def _trace(self, s):
        self.out.write(s)

    # ------------------------------------------------------------------
    # 1. Forward analysis: abstract forward reachability semantics R♮,
    #    computed by induction on the syntax.
    # ------------------------------------------------------------------

    def fwd_stm(self, p, s):
        """R♮[[s]]: the abstract states after statement s, from the abstract states p before it."""
        B = self.B
        if isinstance(s, Assign):
            # R♮[[X ← e]] a = ASSIGN_D[[X ← e]] a
            return p.fwd_assign(s.target, s.value)
        if isinstance(s, Assume):
            # only the states satisfying the condition go on
            return p.filter(s.cond)
        if isinstance(s, Return):
            # program exit: no state reaches the next label
            return B.bot(self.env)
        if isinstance(s, If):
            # R♮[[if e then s1 else s2]] a =
            #     R♮[[s1]](FILTER_D[[e]] a)  ⊔_D  R♮[[s2]](FILTER_D[[not e]] a)
            p1 = self.fwd_blk(p.filter(s.cond), s.then)
            p2 = self.fwd_blk(p.filter(negate(s.cond)), s.orelse)
            return p1.join(p2)
        if isinstance(s, While):
            # R♮[[while e do s done]] a = FILTER_D[[not e]](lfp F♮)
            # where F♮(y) = a ⊔_D R♮[[s]](FILTER_D[[e]] y).
            # The least fixpoint is computed by Kleene iteration from ⊥_D;
            # after `joinfwd` iterations, the join is replaced by a widening
            # to enforce convergence.
            i = B.bot(self.env)
            p2 = self.fwd_blk(i.filter(s.cond), s.body)
            n = 1
            while True:
                i1 = p.join(p2)  # F♮(i)
                if self.tracefwd:
                    self._trace('### %s:%d ###:\np1: %s\ni: %s\np2: %s\ni\': %s\n' % (
                        self._lbl(s.label), n, p, i, p2, i1))
                if i1.is_leq(i):  # post-fixpoint reached: F♮(i) ⊑_D i
                    break
                i = i1 if n <= self.joinfwd else i.widen(i.join(i1))
                if self.tracefwd:
                    self._trace('i\'\': %s\n' % i)
                p2 = self.fwd_blk(i.filter(s.cond), s.body)
                n += 1
            self.fwd[s.label] = i  # loop invariant, at the loop head
            return i.filter(negate(s.cond))
        raise TypeError(s)

    def fwd_blk(self, p, b):
        """R♮[[s1; s2]] = R♮[[s2]] ∘ R♮[[s1]]; records the invariant at each label."""
        for l, s in b.stmts:
            if self.tracefwd:
                self._trace('### %s ###: %s\n' % (self._lbl(l), p))
            self.fwd[l] = p
            p = self.fwd_stm(p, s)
        if self.tracefwd:
            self._trace('### %s ###: %s\n' % (self._lbl(b.end), p))
        self.fwd[b.end] = p
        return p

    # ------------------------------------------------------------------
    # 2. Backward analysis: abstract definite termination semantics R#_M.
    #    The statements are analyzed backwards: from the
    #    ranking function t after a statement, compute the ranking function
    #    before it. Each step of execution (assignment or test) adds 1.
    # ------------------------------------------------------------------

    def bwd_stm(self, p, s, domain=None):
        """R#_M[[s]] t. With -refine, `domain` is the forward invariant R♮
        before s, and the trees are restricted to it."""
        D = self.D
        if isinstance(s, Assign):
            # R#_M[[X ← e]] t = ASSIGN←_A[[X ← e]] t
            return D.bwd_assign(p, s.target, s.value, domain)
        if isinstance(s, Assume):
            return D.filter(p, s.cond, domain)
        if isinstance(s, Return):
            # program exit: 0 steps to termination, everywhere
            return D.zero(domain)
        if isinstance(s, If):
            # R#_M[[if e then s1 else s2]] t =
            #     FILTER_A[[e]](R#_M[[s1]] t)  ⋎_A  FILTER_A[[not e]](R#_M[[s2]] t)
            # The approximation join ⋎_A is undefined (⊥_F) where one of the
            # two branches is undefined, since then termination is not
            # guaranteed.
            p1 = D.filter(self.bwd_blk(p, s.then), s.cond, domain)
            p2 = D.filter(self.bwd_blk(p, s.orelse), negate(s.cond), domain)
            if self.tracebwd:
                self._trace('p1: %s\np2: %s\n' % (D.to_str(p1), D.to_str(p2)))
            return D.join(APPROXIMATION, p1, p2)
        if isinstance(s, While):
            return self._bwd_while(p, s)
        raise TypeError(s)

    def _bwd_while(self, p, s):
        """R#_M[[while e do s done]] t = lfp F#_M
        where F#_M(x) = FILTER_A[[e]](R#_M[[s]] x)  ⋎_A  FILTER_A[[not e]](t).

        The fixpoint is computed by iteration from ⊥ (the totally undefined
        function) with the widening ▿_A after `joinbwd` iterations. Two orders
        are involved:
          - the computational order ⊑_A is used to detect when the iterates
            have stabilized (and to join successive iterates),
          - the approximation order ≼_A is used to check that the limit is
            indeed a fixpoint; otherwise the iteration goes on.
        """
        D = self.D
        l = s.label
        a = self.fwd[l]  # the loop invariant R♮ from the forward analysis
        dm = a if self.refine else None
        p1 = D.filter(p, negate(s.cond), dm)  # FILTER_A[[not e]](t): exiting the loop
        if self.record:
            self.record('exit', l, p1)
        i = D.seeded(self.seeds, dm) if self.seeds else D.bot(dm)
        if self.record:
            self.record('iteration', l, i, n=1, seeded=bool(self.seeds))
        p2 = D.filter(self.bwd_blk(i, s.body), s.cond, dm)  # FILTER_A[[e]](R#_M[[s]] i)
        n = 1
        while True:
            if self.record:
                self.record('body', l, p2, n=n)
            i1 = D.join(APPROXIMATION, p1, p2)  # F#_M(i)
            if self.record:
                self.record('join', l, i1, n=n)
            if self.tracebwd:
                self._trace('### %s:%d ###:\np1: %s\ni: %s\np2: %s\ni\': %s\n' % (
                    self._lbl(l), n, D.to_str(p1), D.to_str(i), D.to_str(p2), D.to_str(i1)))
            # "jokers": a budget of iterations decreasing with n, used by the
            # widening of the leaves to delay the widening of their values
            # (and, for ordinals, the introduction of higher powers of ω; cf.
            # functions.Affine.widen and functions.Ordinals.widen)
            jokers = max(0, self.retrybwd * (self.ordmax + 1) - n + self.joinbwd)
            if D.is_leq(COMPUTATIONAL, i1, i):
                if D.is_leq(APPROXIMATION, i1, i):
                    if self.tracebwd:
                        self._trace('### %s:FIXPOINT ###:\ni: %s\n' % (self._lbl(l), D.to_str(i)))
                    if self.record:
                        self.record('fixpoint', l, i, n=n)
                    break
                i2 = i1 if n <= self.joinbwd else D.widen(i, i1, jokers)
            else:
                i2 = i1 if n <= self.joinbwd else D.widen(i, D.join(COMPUTATIONAL, i, i1), jokers)
            if self.tracebwd:
                self._trace('i\'\': %s\n' % D.to_str(i2))
            if self.record:
                self.record('iteration', l, i2, n=n + 1, widened=n > self.joinbwd)
            p2 = D.filter(self.bwd_blk(i2, s.body), s.cond, dm)
            i = i2
            n += 1
        self.bwd[l] = i  # ranking function at the loop head
        return D.refine(i, a) if self.refine else i

    def bwd_blk(self, p, b):
        """R#_M[[s1; s2]] t = R#_M[[s1]](R#_M[[s2]] t): the statements of a
        block are analyzed in reverse order; records the tree at each label."""
        D = self.D
        a = self.fwd[b.end]
        if self.refine:
            p = D.refine(p, a)
        if self.tracebwd:
            self._trace('### %s ###:\n%s\n' % (self._lbl(b.end), D.to_str(p)))
        if self.record:
            self.record('label', b.end, p)
        self.bwd[b.end] = p
        for l, s in reversed(b.stmts):
            if time.time() - self.start > self.timeout:
                raise Timeout()
            a = self.fwd[l]
            p = self.bwd_stm(p, s, a if self.refine else None)
            if self.refine:
                p = D.refine(p, a)
            if self.tracebwd:
                self._trace('### %s ###:\n%s\n' % (self._lbl(l), D.to_str(p)))
            if self.record:
                self.record('label', l, p, stmt=s)
            self.bwd[l] = p
        return p

    # ------------------------------------------------------------------
    # The whole analysis
    # ------------------------------------------------------------------

    def _init(self, b):
        """Every label starts with the totally undefined ranking function."""
        for l, s in b.stmts:
            self.bwd[l] = self.D.bot()
            if isinstance(s, If):
                self._init(s.then)
                self._init(s.orelse)
            elif isinstance(s, While):
                self.bwd[s.label] = self.D.bot()
                self._init(s.body)
        self.bwd[b.end] = self.D.bot()

    def run(self, precondition=None):
        """Runs the analysis; returns True if termination is proven."""
        Partition.clear_caches()
        body = self.program.body
        self._init(body)
        self.start = time.time()
        # 1. forward analysis, from all possible initial states (⊤_D)
        if self.tracefwd:
            self._trace('\nForward Analysis Trace:\n')
        self.fwd_blk(self.B.top(self.env), body)
        # 2. backward analysis, from the exit of the program, where the
        #    ranking function is LEAF: λX1,...,Xk. 0
        if self.tracebwd:
            self._trace('\nBackward Analysis Trace:\n')
        self.start = time.time()
        self.entry = self.bwd_blk(self.D.zero(), body)
        # 3. termination is proven if the ranking function at the entry is
        #    defined for all the states satisfying the precondition
        cond = precondition if precondition is not None else BConst(True)
        return self.D.defined(self.entry, condition=cond)

    # printing

    @staticmethod
    def _lbl(l):
        return '[%2d:]' % l

    def forward_str(self):
        return '\n'.join('%s: %s' % (self._lbl(l), self.fwd[l]) for l in sorted(self.fwd))

    def backward_str(self):
        return '\n'.join('%s:\n%s\n' % (self._lbl(l), self.D.to_str(self.bwd[l])) for l in sorted(self.bwd))

    def entry_str(self):
        return self.D.to_str(self.entry)
