"""
The piecewise-defined ranking functions abstract domain A (cf. domains/DecisionTree.ml).

Piecewise-defined partial functions are represented by decision trees:

    A = { LEAF: f | f ∈ F } ∪ { NODE{c}: t1; t2 | c ∈ C, t1, t2 ∈ A }

  - the decision nodes are labeled by linear constraints c ∈ C over the
    program variables (in canonical form, see linear.py);
  - the leaf nodes are labeled by functions f ∈ F of the program variables
    (affine or ordinal-valued, see functions.py).

The decision nodes recursively partition the space of possible values of the
program variables: the left subtree t1 of NODE{c} is the part where c holds,
the right subtree t2 the part where ¬c holds. The functions at the leaves
provide upper bounds on the number of execution steps to termination.
The concretization is

    γ_A(t) = γ_A[∅](t)
    γ_A[C](LEAF: f)          = γ_F[α_C(C)](f)
    γ_A[C](NODE{c}: t1; t2)  = γ_A[C ∪ {c}](t1) ∪ γ_A[C ∪ {¬c}](t2)

i.e., the set C of constraints met along a path is turned into an element
α_C(C) of the numerical domain D (here: self.inner(cs)), which is the partition
on which the leaf function is used.

The operators manipulate elements of A_NIL = {NIL} ∪ A, where NIL stands for
"no information" (it is introduced by FILTER_A). NIL is represented
by None.

Implementation notes:
  - the constraints along a path are accumulated in a list `cs`, most recent
    first; `self.inner(cs)` is α_C(cs), and `self.dom(cs, domain)` is
    α_C(cs) ⊓_D domain, where domain is the forward invariant with -refine;
  - each node stores both its constraint c and its negation nc = ¬c, and is
    *normalized*: c is the larger of the two in the total order ≤_C, i.e.,
    nc ≤_C c (both are kept so that ¬c is not recomputed).
"""

from .linear import negate, is_unsat, similar, mentions, constraint_str
from .functions import APPROXIMATION, COMPUTATIONAL
from .syntax import BConst, Maybe, Not, BoolOp, Compare, negate as negate_bexp


class Leaf:
    """LEAF: f"""
    __slots__ = ('f',)

    def __init__(self, f):
        self.f = f


class Node:
    """NODE{c}: l; r  (l where c holds, r where nc = ¬c holds)"""
    __slots__ = ('c', 'nc', 'l', 'r')

    def __init__(self, c, nc, l, r):
        self.c = c
        self.nc = nc
        self.l = l
        self.r = r


def lkey(c, nc):
    """Total order on decision node labels (cf. module L): a node is
    identified by the larger of its constraint and of its negation, so that
    NODE{c} and NODE{¬c} are recognized as the same decision."""
    return c if nc <= c else nc


def _cmp(a, b):
    return (a > b) - (a < b)


class DT:
    """An element of the ranking functions abstract domain: a decision tree,
    possibly restricted to a set of reachable states (option -refine)."""

    __slots__ = ('domain', 'tree')

    def __init__(self, domain, tree):
        self.domain = domain  # reachable states (a partition) or None
        self.tree = tree


class DecisionTree:
    """The abstract domain A, parameterized by the numerical domain B (for
    the partitions) and by the function domain F (for the leaves)."""

    def __init__(self, B, F, env, retrybwd=5, trace=None):
        self.B = B  # partition domain (class)
        self.F = F  # function domain (instance)
        self.env = env
        self.retrybwd = retrybwd
        self.trace = trace
        self.record = None  # record(kind, tree): the steps of the widening (see web.py)

    # helpers

    def inner(self, cs):
        """α_C(cs): the element of D represented by a set of constraints."""
        return self.B.inner(self.env, cs)

    def dom(self, cs, domain):
        """The partition α_C(cs), restricted to the reachable states (if any)."""
        b = self.B.inner(self.env, cs)
        return b if domain is None else b.meet(domain)

    def redundant(self, c, cs):
        """c is redundant with respect to cs: α_C(cs) ⊑_D α_C({c}).
        (¬c is redundant iff c contradicts cs.)"""
        return self.inner(cs).is_leq(self.inner([c]))

    @staticmethod
    def labels(t):
        """The set of the constraints labeling the nodes of t."""
        ls = {}

        def aux(t):
            if isinstance(t, Node):
                aux(t.l)
                aux(t.r)
                ls.setdefault(lkey(t.c, t.nc), (t.c, t.nc))
        aux(t)
        return ls

    # constructors

    def bot(self, domain=None):
        """LEAF: ⊥_F, the totally undefined function (start of the fixpoint iterations)."""
        return DT(domain, Leaf(self.F.bot()))

    def seeded(self, cs, domain=None):
        """⊥_F split on the constraints cs (the seeds): the start of the
        fixpoint iterations with option -seed. It is the same function as
        LEAF: ⊥_F, but its decision nodes are never removed by the domain
        widening (left unification keeps the constraints of the previous
        iterate), so the partitions of the ranking function can always be
        split on the seeds: they are thresholds for the domain widening."""
        t = Leaf(self.F.bot())
        for c in cs:
            nc = negate(c)
            t = Node(c, nc, t, t) if nc <= c else Node(nc, c, t, t)
        return DT(domain, self.sort_tree(t))

    def zero(self, domain=None):
        """LEAF: λX1,...,Xk. 0, the ranking function at the program exit."""
        return DT(domain, Leaf(self.F.zero()))

    def top(self, domain=None):
        """LEAF: ⊤_F, the function that is undefined because of a lack of precision."""
        return DT(domain, Leaf(self.F.top()))

    # sorting

    def sort_tree(self, t):
        """Sorts a decision tree, so that the constraints along each path are
        increasing with respect to ≤_C (and the nodes are normalized).

        The operators below rely on this invariant: e.g. tree unification
        compares the roots of the two trees to decide which constraint comes
        first. Sorting is needed after ASSIGN←_A, which replaces the
        constraints by their pre-images. `_swap` moves the smallest
        constraint of a tree to its root; this is then repeated on the
        subtrees."""
        st = self._swap(t)
        if isinstance(st, Node):
            return Node(st.c, st.nc, self.sort_tree(st.l), self.sort_tree(st.r))
        return st

    def _swap(self, t):
        """Brings the smallest constraint of t (w.r.t. ≤_C) to the root.

        The cases compare the constraint c of the root with the roots c1, c2
        of the (already swapped) subtrees: when c is larger, the root is
        pushed below c1 (or c2), duplicating it in both branches. A few cases
        exploit "similar" constraints (same coefficients, different constant,
        e.g. x >= 1 and x >= 3), for which one of the combinations is known to
        be infeasible, to avoid useless duplications. The second half handles
        non-normalized nodes (¬c >_C c) by swapping c with ¬c and the two
        subtrees."""
        if not isinstance(t, Node):
            return t
        c, nc = t.c, t.nc
        sl = self._swap(t.l)
        sr = self._swap(t.r)
        ln = isinstance(sl, Node)
        rn = isinstance(sr, Node)
        if ln:
            c1, nc1, l1, r1 = sl.c, sl.nc, sl.l, sl.r
        if rn:
            c2, nc2, l2, r2 = sr.c, sr.nc, sr.l, sr.r
        if nc <= c:  # t is normalized
            rt = (c, nc)
            if ln and rn and c1 == c2:
                if c <= c1:
                    if c == c1:
                        return Node(c, nc, l1, r2)
                    return Node(c, nc, sl, sr)
                if similar(c, c1):
                    return Node(c1, nc1, l1, Node(c, nc, r1, r2))
                return Node(c1, nc1, Node(*rt, l1, l2), Node(*rt, r1, r2))
            if ln and rn and c1 <= c2:
                if c <= c1:
                    if c == c1:
                        return Node(c, nc, l1, sr)
                    return Node(c, nc, sl, sr)
                if c <= c2:
                    if c == c2:
                        if similar(c, c1):
                            return Node(c1, nc1, l1, Node(c, nc, r1, r2))
                        return Node(c1, nc1, Node(*rt, l1, r2), Node(*rt, r1, r2))
                    if similar(c2, c) and similar(c, c1):
                        return Node(c1, nc1, l1, Node(c, nc, r1, sr))
                    return Node(c1, nc1, Node(*rt, l1, sr), Node(*rt, r1, sr))
                if similar(c, c2) and similar(c2, c1):
                    return Node(c1, nc1, l1, Node(c, nc, r1, r2))
                return Node(c1, nc1,
                            Node(c2, nc2, Node(*rt, l1, l2), Node(*rt, l1, r2)),
                            Node(c2, nc2, Node(*rt, r1, l2), Node(*rt, r1, r2)))
            if ln and rn:  # c1 > c2
                if c <= c2:
                    if c == c2:
                        return Node(c, nc, sl, r2)
                    return Node(c, nc, sl, sr)
                if c <= c1:
                    if c == c1:
                        if similar(c, c2):
                            return Node(c, nc, l1, r2)
                        return Node(c2, nc2, Node(*rt, l1, l2), Node(*rt, l1, r2))
                    if similar(c1, c) and similar(c, c2):
                        return Node(c, nc, l1, r2)
                    return Node(c2, nc2, Node(*rt, sl, l2), Node(*rt, sl, r2))
                if similar(c, c1) and similar(c1, c2):
                    return Node(c1, nc1, l1, Node(c, nc, r1, r2))
                return Node(c2, nc2,
                            Node(c1, nc1, Node(*rt, l1, l2), Node(*rt, r1, l2)),
                            Node(c1, nc1, Node(*rt, l1, r2), Node(*rt, r1, r2)))
            if ln:
                if c <= c1:
                    if c == c1:
                        return Node(c, nc, l1, sr)
                    return Node(c, nc, sl, sr)
                if similar(c, c1):
                    return Node(c1, nc1, l1, Node(c, nc, r1, sr))
                return Node(c1, nc1, Node(*rt, l1, sr), Node(*rt, r1, sr))
            if rn:
                if c <= c2:
                    if c == c2:
                        return Node(c, nc, sl, r2)
                    return Node(c, nc, sl, sr)
                if similar(c, c2):
                    return Node(c, nc, sl, r2)
                return Node(c2, nc2, Node(*rt, sl, l2), Node(*rt, sl, r2))
            return Node(c, nc, sl, sr)
        # t is not normalized
        rt = (nc, c)
        if ln and rn and c1 == c2:
            if nc <= c1:
                if nc == c1:
                    return Node(nc, c, l2, r1)
                return Node(nc, c, sr, sl)
            if similar(nc, c1):
                return Node(c1, nc1, l2, Node(nc, c, r2, r1))
            return Node(c1, nc1, Node(*rt, l2, l1), Node(*rt, r2, r1))
        if ln and rn and c1 <= c2:
            if nc <= c1:
                if nc == c1:
                    return Node(nc, c, sr, r1)
                return Node(nc, c, sr, sl)
            if nc <= c2:
                if nc == c2:
                    if similar(nc, c1):
                        return Node(nc, c, l2, r1)
                    return Node(c1, nc1, Node(*rt, l2, l1), Node(*rt, l2, r1))
                if similar(c2, nc) and similar(nc, c1):
                    return Node(nc, c, l2, r1)
                return Node(c1, nc1, Node(*rt, sr, l1), Node(*rt, sr, r1))
            if similar(nc, c2) and similar(c2, c1):
                return Node(c2, nc2, l2, Node(nc, c, r2, r1))
            return Node(c1, nc1,
                        Node(c2, nc2, Node(*rt, l2, l1), Node(*rt, r2, l1)),
                        Node(c2, nc2, Node(*rt, l2, r1), Node(*rt, r2, r1)))
        if ln and rn:  # c1 > c2
            if nc <= c2:
                if nc == c2:
                    return Node(nc, c, l2, sl)
                return Node(nc, c, sr, sl)
            if nc <= c1:
                if nc == c1:
                    if similar(nc, c2):
                        return Node(c2, nc2, l2, Node(nc, c, r2, r1))
                    return Node(c2, nc2, Node(*rt, l2, r1), Node(*rt, r2, r1))
                if similar(c1, nc) and similar(nc, c2):
                    return Node(c2, nc2, l2, Node(nc, c, r2, sl))
                return Node(c2, nc2, Node(*rt, l2, sl), Node(*rt, r2, sl))
            if similar(nc, c1) and similar(c1, c2):
                return Node(c2, nc2, l2, Node(nc, c, r2, r1))
            return Node(c2, nc2,
                        Node(c1, nc1, Node(*rt, l2, l1), Node(*rt, l2, r1)),
                        Node(c1, nc1, Node(*rt, r2, l1), Node(*rt, r2, r1)))
        if ln:
            if nc <= c1:
                if nc == c1:
                    return Node(nc, c, sr, r1)
                return Node(nc, c, sr, sl)
            if similar(nc, c1):
                return Node(nc, c, sr, r1)
            return Node(c1, nc1, Node(*rt, sr, l1), Node(*rt, sr, r1))
        if rn:
            if nc <= c2:
                if nc == c2:
                    return Node(nc, c, l2, sl)
                return Node(nc, c, sr, sl)
            if similar(nc, c2):
                return Node(c2, nc2, l2, Node(nc, c, r2, sl))
            return Node(c2, nc2, Node(*rt, l2, sl), Node(*rt, r2, sl))
        return Node(nc, c, sr, sl)

    # unification

    def unify(self, t1, t2, cs=()):
        """Tree unification: finds a common refinement of two (sorted)
        decision trees, i.e., returns two trees with the same decision nodes,
        equivalent to t1 and t2 respectively.

        The constraints cs encountered along the path are accumulated, and
        are used to remove the decision nodes that become redundant (the cases
        a and b below) or unreachable."""
        cs = list(cs)
        n1 = isinstance(t1, Node)
        n2 = isinstance(t2, Node)
        if not n1 and not n2:
            # base cases: leaves or NIL; the whole partition may be empty
            if t1 is None and t2 is None:
                return (None, None)
            if self.inner(cs).is_bot():
                return (None, None)
            return (t1, t2)
        if n1 and n2 and t1.c == t2.c:
            # case 3: same constraint at the root of both trees
            ul1, ul2 = self.unify(t1.l, t2.l, [t1.c] + cs)
            ur1, ur2 = self.unify(t1.r, t2.r, [t1.nc] + cs)
            return (Node(t1.c, t1.nc, ul1, ur1), Node(t2.c, t2.nc, ul2, ur2))
        if n1 and (not n2 or t1.c <= t2.c):
            # case 2: the root c1 of t1 comes first (c1 <_C c2): c1 is added to t2
            c1, nc1 = t1.c, t1.nc
            if self.redundant(c1, cs):    # 2a: c1 is redundant, keep only the left subtree
                return self.unify(t1.l, t2, cs)
            if self.redundant(nc1, cs):   # 2b: ¬c1 is redundant, keep only the right subtree
                return self.unify(t1.r, t2, cs)
            ul1, ul2 = self.unify(t1.l, t2, [c1] + cs)
            ur1, ur2 = self.unify(t1.r, t2, [nc1] + cs)
            return (Node(c1, nc1, ul1, ur1), Node(c1, nc1, ul2, ur2))
        # case 1 (symmetric): the root c2 of t2 comes first: c2 is added to t1
        c2, nc2 = t2.c, t2.nc
        if self.redundant(c2, cs):    # 1a: c2 is redundant
            return self.unify(t1, t2.l, cs)
        if self.redundant(nc2, cs):   # 1b: ¬c2 is redundant
            return self.unify(t1, t2.r, cs)
        # 1c: c2 is added to t1
        ul1, ul2 = self.unify(t1, t2.l, [c2] + cs)
        ur1, ur2 = self.unify(t1, t2.r, [nc2] + cs)
        return (Node(c2, nc2, ul1, ur1), Node(c2, nc2, ul2, ur2))

    # orderings

    def is_leq(self, k, t1, t2):
        """The orders on A, k ∈ {APPROXIMATION, COMPUTATIONAL}:

          1. perform tree unification;
          2. descend the trees accumulating the constraints C along the paths;
          3. compare the leaves with the approximation order ≼_F[α_C(C)]
             or with the computational order ⊑_F[α_C(C)].

        The approximation order t1 ≼_A t2 requires dom(t1) ⊇ dom(t2) and
        t1 ≤ t2 on dom(t2): it is the order of the ranking functions.
        The computational order treats ⊥_F as the least element."""
        domain = t1.domain
        F = self.F

        def aux(t1, t2, cs):
            if t1 is None and t2 is None:
                return True
            if t1 is None or t2 is None:
                return self.dom(cs, domain).is_bot()
            if isinstance(t1, Leaf) and isinstance(t2, Leaf):
                b = self.dom(cs, domain)
                if b.is_bot():
                    return True
                f1, f2 = t1.f, t2.f
                if k == APPROXIMATION:
                    # f1 ≼_F f2: f1 must be defined wherever f2 is, and smaller there
                    if not F.defined(f2) or F.defined(f1):
                        if F.defined(f1) and F.defined(f2):
                            return F.is_leq(k, b, f1, f2)
                        return True
                    return False
                return F.is_leq(k, b, f1, f2)
            if isinstance(t1, Node) and isinstance(t2, Node) and t1.c == t2.c:
                return aux(t1.l, t2.l, [t1.c] + cs) and aux(t1.r, t2.r, [t1.nc] + cs)
            raise ValueError('is_leq: unexpected tree structure')

        u1, u2 = self.unify(t1.tree, t2.tree)
        return aux(u1, u2, [])

    # binary operators

    def _join_helper(self, f_bot_left, f_bot_right, f_leaf, t1, t2):
        """Common skeleton of join and meet: unify the trees, then combine the
        leaves with f_leaf; f_bot_left/f_bot_right say what to do when one of
        the two trees is NIL."""
        def aux(t1, t2, cs):
            if t1 is None and t2 is None:
                return None
            if isinstance(t1, Leaf) and t2 is None:
                return f_bot_right(cs, t1.f)
            if t1 is None and isinstance(t2, Leaf):
                return f_bot_left(cs, t2.f)
            if isinstance(t1, Leaf) and isinstance(t2, Leaf):
                return f_leaf(cs, t1.f, t2.f)
            if isinstance(t1, Node) and isinstance(t2, Node):
                return Node(t1.c, t1.nc, aux(t1.l, t2.l, [t1.c] + cs), aux(t1.r, t2.r, [t1.nc] + cs))
            raise ValueError('join: unexpected tree structure')

        u1, u2 = self.unify(t1, t2)
        return aux(u1, u2, [])

    def join(self, k, t1, t2):
        """The approximation join ⋎_A and the computational join ⊔_A:
        NIL ⋎ t = t ⋎ NIL = t, and the leaves are joined
        with ⋎_F[α_C(C)] or ⊔_F[α_C(C)]. The two differ in how undefined
        leaves are treated: ⊥_F ⋎_F f = ⊥_F, but ⊥_F ⊔_F f = f."""
        domain = t1.domain

        def f_bot(cs, f):
            return None if self.dom(cs, domain).is_bot() else Leaf(f)

        def f_leaf(cs, f1, f2):
            b = self.dom(cs, domain)
            return None if b.is_bot() else Leaf(self.F.join(k, b, f1, f2))

        return DT(domain, self._join_helper(f_bot, f_bot, f_leaf, t1.tree, t2.tree))

    def meet(self, k, t1, t2):
        """The meet ⋏_A: NIL ⋏ t = t ⋏ NIL = NIL, and the
        leaves are joined with the approximation join ⋎_F[α_C(C)].
        It is used by FILTER_A for conjunctions (with k = APPROXIMATION)."""
        domain = t1.domain
        bot_leaf = Leaf(self.F.bot())

        def f_bot(cs, f):
            return None if k == APPROXIMATION else bot_leaf

        def f_leaf(cs, f1, f2):
            b = self.dom(cs, domain)
            return None if b.is_bot() else Leaf(self.F.join(APPROXIMATION, b, f1, f2))

        return DT(domain, self._join_helper(f_bot, f_bot, f_leaf, t1.tree, t2.tree))

    def left_unification(self, t1, t2, domain, join_kind=COMPUTATIONAL):
        """Left unification, used for the domain widening:
        a variant of tree unification that forces the structure of t1 on t2.
        The decision nodes of t2 whose constraint does not appear in t1 are
        removed, and the corresponding subtrees are joined (case 1c:
        L2 ⊔_A R2). This bounds the size of the trees across the iterations.

        Implementation: the constraints of t2 that do not occur in t1 (`ls`)
        are first pushed to the bottom of t2 (`rebalance`, using the order
        `cmp` in which they come after all the others); then the two trees
        are unified, collapsing the subtrees of t2 that only depend on the
        constraints in `ls` (`collapse`)."""
        ls1 = self.labels(t1)
        ls2 = self.labels(t2)
        ls = set(ls2) - set(ls1)
        F = self.F

        def cmp(l1, l2):
            k1, k2 = lkey(*l1), lkey(*l2)
            m1, m2 = k1 in ls, k2 in ls
            if m1 == m2:
                return _cmp(k1, k2)
            return -1 if m2 else 1

        def remove_redundant(t, cs):
            if not isinstance(t, Node):
                return t
            if self.redundant(t.c, cs):
                return remove_redundant(t.l, cs)
            if self.redundant(t.nc, cs):
                return remove_redundant(t.r, cs)
            return Node(t.c, t.nc, remove_redundant(t.l, [t.c] + cs), remove_redundant(t.r, [t.nc] + cs))

        def add_node(c, nc, l, r, cs):
            if self.redundant(c, cs):
                return l
            if self.redundant(nc, cs):
                return r
            return Node(c, nc, l, r)

        def make_node(c, nc, l, r, cs):
            def smallest(t, cc):
                if isinstance(t, Node) and cmp(cc, (t.c, t.nc)) > 0:
                    return (t.c, t.nc)
                return cc

            if self.redundant(c, cs):
                return l
            if self.redundant(nc, cs):
                return r
            sc = smallest(l, smallest(r, (c, nc)))
            ln = isinstance(l, Node) and cmp((l.c, l.nc), sc) == 0
            rn = isinstance(r, Node) and cmp((r.c, r.nc), sc) == 0
            if ln and rn:
                return Node(l.c, l.nc, make_node(c, nc, l.l, r.l, [l.c] + cs),
                            make_node(c, nc, l.r, r.r, [l.nc] + cs))
            if ln:
                return Node(l.c, l.nc, make_node(c, nc, l.l, r, [l.c] + cs),
                            make_node(c, nc, l.r, r, [l.nc] + cs))
            if rn:
                return Node(r.c, r.nc, make_node(c, nc, l, r.l, [r.c] + cs),
                            make_node(c, nc, l, r.r, [r.nc] + cs))
            return Node(c, nc, l, r)

        def rebalance(t, cs):
            if not isinstance(t, Node):
                return t
            ll = rebalance(t.l, [t.c] + cs)
            rr = rebalance(t.r, [t.nc] + cs)
            return make_node(t.c, t.nc, ll, rr, cs)

        def collapse(t, cs):
            if not isinstance(t, Node):
                return t
            assert lkey(t.c, t.nc) in ls
            if self.redundant(t.c, cs):
                return collapse(t.l, cs)
            if self.redundant(t.nc, cs):
                return collapse(t.r, cs)
            ll = collapse(t.l, [t.c] + cs)
            rr = collapse(t.r, [t.nc] + cs)
            if rr is None:
                return ll
            if ll is None:
                return rr
            if isinstance(ll, Leaf) and isinstance(rr, Leaf):
                b = self.dom(cs, domain)
                return Leaf(F.join(join_kind, b, ll.f, rr.f))
            raise AssertionError('left_unification: collapse')

        def lunify(t1, t2, cs):
            n1 = isinstance(t1, Node)
            n2 = isinstance(t2, Node)
            if not n1 and not n2:
                return t2
            if n1 and not n2:
                return add_node(t1.c, t1.nc, lunify(t1.l, t2, [t1.c] + cs), lunify(t1.r, t2, [t1.nc] + cs), cs)
            if not n1 and n2:
                if lkey(t2.c, t2.nc) in ls:
                    return collapse(t2, cs)
                return add_node(t2.c, t2.nc, lunify(t1, t2.l, [t2.c] + cs), lunify(t1, t2.r, [t2.nc] + cs), cs)
            w = cmp((t1.c, t1.nc), (t2.c, t2.nc))
            if w == 0:
                return add_node(t1.c, t1.nc, lunify(t1.l, t2.l, [t1.c] + cs), lunify(t1.r, t2.r, [t1.nc] + cs), cs)
            if w < 0:
                return add_node(t1.c, t1.nc, lunify(t1.l, t2, [t1.c] + cs), lunify(t1.r, t2, [t1.nc] + cs), cs)
            assert lkey(t2.c, t2.nc) not in ls
            return add_node(t2.c, t2.nc, lunify(t1, t2.l, [t2.c] + cs), lunify(t1, t2.r, [t2.nc] + cs), cs)

        return lunify(t1, remove_redundant(rebalance(t2, []), []), [])

    def widen(self, d1, d2, jokers=0):
        """The widening ▿_A. Its goal is to *predict* a valid
        ranking function; the prediction can temporarily be wrong
        (under-approximate the value, or over-approximate the domain) and is
        corrected by the next iterations. Steps (t1 is the previous iterate,
        t2 the current one):

          1. widen_right: the leaves where the ranking function is not
             stable (the old leaf is not below the new one, in the
             computational order) are set to ⊤_F. This is the check for
             case A (wrong domain prediction: a defined leaf f became ⊥_F,
             and f ⋢_F ⊥_F) and for cases B and C (wrong value prediction:
             the value decreased somewhere);
          2. left_unification: domain widening, the structure of t1 is
             forced on t2;
          3. tree unification of t1 and t2;
          4. widen_up: the corresponding leaves are widened with ▿_F;
          5. widen_leaves: value widening: each leaf that changed
             is extrapolated with respect to its adjacent leaves in t1, with
             the extrapolation operator ▾_F (functions F.extend).
        """
        domain = d1.domain
        t1, t2 = d1.tree, d2.tree

        def ts(t):
            return self.tree_str(t)

        if self.trace:
            self.trace('WIDENING\nt1: %s\n\nt2: %s\n' % (ts(t1), ts(t2)))
        rec = self.record
        if rec:
            rec('widen_t1', DT(domain, t1))
            rec('widen_t2', DT(domain, t2))
        t2 = self.widen_right(t1, t2, domain)
        if self.trace:
            self.trace('\nt2[widen_right]: %s\n' % ts(t2))
        if rec:
            rec('widen_right', DT(domain, t2))
        t2 = self.left_unification(t1, t2, domain)
        if self.trace:
            self.trace('\nt2[left_unification]: %s\n' % ts(t2))
        if rec:
            rec('left_unification', DT(domain, t2))
        t1, t2 = self.unify(t1, t2)
        if self.trace:
            self.trace('\nt1[tree_unification]: %s\n\nt2[tree_unification]: %s\n' % (ts(t1), ts(t2)))
        t2 = self.widen_up(t1, t2, domain, jokers)
        if self.trace:
            self.trace('\nt2[widen_up]: %s\n' % ts(t2))
        if rec:
            rec('widen_up', DT(domain, t2))
        r = DT(domain, self.widen_leaves(t1, t2, domain))
        if rec:
            rec('widen_leaves', r)
        return r

    def widen_right(self, t1, t2, domain=None):
        """Step 1 of the widening, check for cases A, B and C: the leaves of
        t2 that are not above the corresponding leaves of t1 in the
        computational order are set to ⊤_F. Since ⊥_F is the least element
        of ⊑_F, this catches both a defined leaf that became ⊥_F (case A)
        and a defined value that decreased (cases B and C). Same traversal as
        tree unification, adding the nodes of t1 to t2."""
        F = self.F

        def widen_right(t1, t2, cs):
            # step 1 (same traversal as tree unification, adding the nodes of t1 to t2)
            if isinstance(t1, Leaf) and isinstance(t2, Leaf):
                b = self.dom(cs, domain)
                return t2 if F.is_leq(COMPUTATIONAL, b, t1.f, t2.f) else Leaf(F.top())
            n1 = isinstance(t1, Node)
            n2 = isinstance(t2, Node)
            if n1 and n2 and t1.c == t2.c:
                return Node(t2.c, t2.nc, widen_right(t1.l, t2.l, [t1.c] + cs), widen_right(t1.r, t2.r, [t1.nc] + cs))
            if n1 and (not n2 or t1.c <= t2.c):
                if self.redundant(t1.c, cs):
                    return widen_right(t1.l, t2, cs)
                if self.redundant(t1.nc, cs):
                    return widen_right(t1.r, t2, cs)
                return Node(t1.c, t1.nc, widen_right(t1.l, t2, [t1.c] + cs), widen_right(t1.r, t2, [t1.nc] + cs))
            if n2:
                return Node(t2.c, t2.nc, widen_right(t1, t2.l, [t2.c] + cs), widen_right(t1, t2.r, [t2.nc] + cs))
            return t2

        return widen_right(t1, t2, [])

    def widen_up(self, t1, t2, domain=None, jokers=0):
        """Step 4 of the widening: the leaves of the (unified) trees t1 and t2
        are widened with ▿_F (the jokers delay the widening of ordinals)."""
        F = self.F
        retry = self.retrybwd

        def widen_up(t1, t2, cs):
            if t1 is None and t2 is None:
                return None
            if isinstance(t1, Leaf) and isinstance(t2, Leaf):
                b = self.dom(cs, domain)
                j = (jokers + retry - 1) // retry if retry > 0 else 0
                return Leaf(F.widen(b, t1.f, t2.f, jokers=j))
            n1 = isinstance(t1, Node)
            n2 = isinstance(t2, Node)
            if n1 and n2 and t1.c == t2.c:
                return Node(t1.c, t1.nc, widen_up(t1.l, t2.l, [t1.c] + cs), widen_up(t1.r, t2.r, [t1.nc] + cs))
            if n1 and (not n2 or t1.c <= t2.c):
                if self.redundant(t1.c, cs):
                    return widen_up(t1.l, t2, cs)
                if self.redundant(t1.nc, cs):
                    return widen_up(t1.r, t2, cs)
                return Node(t1.c, t1.nc, widen_up(t1.l, t2, [t1.c] + cs), widen_up(t1.r, t2, [t1.nc] + cs))
            if n2:
                return Node(t2.c, t2.nc, widen_up(t1, t2.l, [t2.c] + cs), widen_up(t1, t2.r, [t2.nc] + cs))
            return None

        return widen_up(t1, t2, [])

    def widen_leaves(self, t1, t2, domain=None):
        """Step 5 of the widening, value widening: each leaf of t2 that
        changed with respect to the (unified) tree t1 is extrapolated with
        respect to its adjacent leaves in t1, with ▾_F (F.extend)."""
        F = self.F

        def widen_leaves(t1, t2):
            # a path in the tree is encoded as a list with one entry per
            # label of t2 (in increasing order): 1 = the constraint holds,
            # 2 = its negation holds, 0 = not tested
            prev = t1
            lbl = [p for _, p in sorted(self.labels(t2).items())]

            def leaves(p, t, ls, cs):
                # the defined leaves of t reached by following the path p
                # (with the partition on which they are defined)
                if t is None:
                    return []
                if isinstance(t, Leaf) and not ls:
                    f = t.f
                    b = self.dom(cs, domain)
                    if F.defined(f) and not b.is_bot() and not F.is_eq(b, f, F.reset(f)):
                        return [(b, f)]
                    return []
                c, nc = ls[0]
                h = p[0]
                if isinstance(t, Node) and t.c == c:
                    if h == 2:
                        return leaves(p[1:], t.r, ls[1:], [t.nc] + cs)
                    return leaves(p[1:], t.l, ls[1:], [t.c] + cs)
                if isinstance(t, Leaf) or c <= t.c:
                    if h == 1:
                        return leaves(p[1:], t, ls[1:], [c] + cs)
                    if h == 2:
                        return leaves(p[1:], t, ls[1:], [nc] + cs)
                    return leaves(p[1:], t, ls[1:], cs)
                raise ValueError('widen: leaves')

            def adjacent(p1, p2):
                # the leaves of the previous iterate reached by the path p1 + p2,
                # and by the paths obtained by flipping one of the decisions
                # in p2 (i.e., the leaves adjacent to it)
                res = []
                while p2:
                    h, ps = p2[0], p2[1:]
                    if h == 1:
                        res.extend(leaves(p1 + [2] + ps, prev, lbl, []))
                        p1 = p1 + [1]
                    elif h == 2:
                        res.extend(leaves(p1 + [1] + ps, prev, lbl, []))
                        p1 = p1 + [2]
                    else:
                        p1 = p1 + [0]
                    p2 = ps
                res.extend(leaves(p1, prev, lbl, []))
                return res

            def extend(b2, f2, bfs):
                # joins the extrapolations ▾_F[b1, b2](f1, f2) of f2 (defined on
                # b2) with respect to each adjacent leaf f1 (defined on b1)
                if not bfs:
                    return f2
                b1, f1 = bfs[0]
                if self.trace:
                    self.trace('EXTEND\n%s ? %s\n%s ? %s\n%s ? %s\n' % (
                        b1, F.to_str(f1), b2, F.to_str(f2), b2, F.to_str(F.extend(b1, b2, f1, f2))))
                return F.join(COMPUTATIONAL, b2, F.extend(b1, b2, f1, f2), extend(b2, f2, bfs[1:]))

            def merge(t1, t2, cs):
                if t2 is None:
                    return t1
                if t1 is None:
                    return t2
                if isinstance(t1, Leaf) and isinstance(t2, Leaf):
                    return Leaf(F.join(COMPUTATIONAL, self.inner(cs), t1.f, t2.f))
                if isinstance(t1, Node) and isinstance(t2, Node) and t1.c == t2.c:
                    return Node(t1.c, t1.nc, merge(t1.l, t2.l, [t1.c] + cs), merge(t1.r, t2.r, [t1.nc] + cs))
                raise ValueError('widen: merge')

            def aux(p, ls, t1, t2, cs):
                # descends t1 and t2 (unified) recording the path p (reversed)
                if t1 is None and t2 is None:
                    return None
                if isinstance(t1, Leaf) and isinstance(t2, Leaf):
                    b = self.dom(cs, domain)
                    if b.is_bot():
                        return None
                    if F.is_eq(b, t1.f, t2.f):  # stable leaf: nothing to extrapolate
                        return t2
                    path = list(reversed(p)) + [0] * len(ls)
                    bfs = adjacent([], path)
                    return Leaf(extend(b, t2.f, bfs))
                if isinstance(t1, Node) and isinstance(t2, Node) and ls and t1.c == t2.c:
                    c, nc = ls[0]
                    if t1.c == c:
                        return Node(t1.c, t1.nc, aux([1] + p, ls[1:], t1.l, t2.l, [t1.c] + cs),
                                    aux([2] + p, ls[1:], t1.r, t2.r, [t1.nc] + cs))
                    if c <= t1.c:
                        if self.redundant(c, cs):
                            return aux([0] + p, ls[1:], t1, t2, cs)
                        return merge(aux([1] + p, ls[1:], t1, t2, [c] + cs),
                                     aux([2] + p, ls[1:], t1, t2, [nc] + cs), cs)
                return None

            return aux([], lbl, t1, t2, [])

        return widen_leaves(t1, t2)

    # transfer functions

    def bwd_assign(self, t, x, e, domain=None):
        """The backward assignment ASSIGN←_A[[X ← e]].

          - leaves: ASSIGN←_F[[X ← e]] on the defined leaves (substitution of
            e for X in the function, plus one step);
          - decision nodes whose constraint c mentions X: c and ¬c are replaced
            by their pre-images I = α_C(ASSIGN←_D[[X ← e]](γ_C(c))) and
            J = α_C(ASSIGN←_D[[X ← e]](γ_C(¬c))), which are sets of
            constraints; there are four cases:
              1. I = J = ∅ (both are always true): L ⋎_A R
              2. I = ∅, ⊥_C ∈ J (c always holds after the assignment): L
              3. ⊥_C ∈ I, J = ∅ (c never holds): R
              4. otherwise: prune L with I and R with J, and join with ⋎_A
            The approximation join ⋎_A makes the result undefined where the
            pre-images of c and ¬c overlap (because of non-determinism) and
            one of the two subtrees is undefined;
          - the other decision nodes are left unchanged.

        With -refine, `domain` (pre) is the forward invariant before the
        assignment, and t.domain (post) the one after it: the pre-images are
        computed from the reachable states only."""
        B, F, env = self.B, self.F, self.env
        pre = domain
        post = t.domain
        cache = {}
        i = env.index[x]

        def merge(t1, t2, cs):
            # approximation join ⋎_A of two trees (below the path cs)
            def aux(t1, t2, cs):
                if t2 is None:
                    return t1
                if t1 is None:
                    return t2
                if isinstance(t1, Leaf) and isinstance(t2, Leaf):
                    b = self.dom(cs, pre)
                    return Leaf(F.join(APPROXIMATION, b, t1.f, t2.f))
                if isinstance(t1, Node) and isinstance(t2, Node) and t1.c == t2.c:
                    return Node(t1.c, t1.nc, aux(t1.l, t2.l, [t1.c] + cs), aux(t1.r, t2.r, [t1.nc] + cs))
                raise ValueError('bwd_assign: merge')

            u1, u2 = self.unify(t1, t2, cs)
            return aux(u1, u2, cs)

        def build(t, cs):
            # prunes t with a set cs of constraints: a chain of decision nodes,
            # with t on the side where all of them hold and NIL elsewhere
            if not cs:
                return t
            c = cs[0]
            nc = negate(c)
            if nc <= c:
                return Node(c, nc, build(t, cs[1:]), None)
            return Node(nc, c, None, build(t, cs[1:]))

        def filter_constraints(cs, d):
            # with -refine: drops the constraints that are redundant or
            # contradictory with respect to the reachable states d
            out = []
            for c in cs:
                b = self.inner([c])
                if not is_unsat(c) and (d.is_leq(b) or d.meet(b).is_bot()):
                    continue
                out.insert(0, c)
            return out

        def pre_image(c):
            # α_C(ASSIGN←_D[[X ← e]](γ_C(c))): the constraints that must hold
            # before the assignment for c to hold after it
            if pre is not None and post is not None:
                r = self.inner([c]).meet(post).bwd_assign(x, e).constraints()
                return filter_constraints(r, pre)
            return self.inner([c]).bwd_assign(x, e).constraints()

        def aux(t, cs):
            if t is None:
                return None
            if isinstance(t, Leaf):
                if self.inner(cs).is_bot():
                    return None
                return Leaf(F.bwd_assign(t.f, x, e))
            c, nc, l, r = t.c, t.nc, t.l, t.r
            if not mentions(c, i):
                # the assignment does not affect c
                return Node(c, nc, aux(l, [c] + cs), aux(r, [nc] + cs))
            if c in cache:
                cc, ncc = cache[c]
            else:
                cc, ncc = pre_image(c), pre_image(nc)  # I and J
                cache[c] = (cc, ncc)
            if not cc and not ncc:  # case 1
                return merge(aux(l, cs), aux(r, cs), cs)
            if not cc and len(ncc) == 1 and is_unsat(ncc[0]):  # case 2
                return aux(l, cs)
            if len(cc) == 1 and not ncc and is_unsat(cc[0]):  # case 3
                return aux(r, cs)
            # case 4
            if len(cc) == 1 and len(ncc) == 1:
                # (common special case: I and J are single constraints,
                # complementary when the assignment is deterministic)
                x1, y = cc[0], ncc[0]
                if is_unsat(x1) and is_unsat(y):
                    return Leaf(F.bot())
                nx = negate(x1)
                ny = negate(y)
                ll = aux(l, [x1] + cs)
                rr = aux(r, [y] + cs)
                if nx == y:
                    return self.sort_tree(Node(x1, nx, ll, rr))
                return merge(self.sort_tree(Node(x1, nx, ll, rr)), self.sort_tree(Node(y, ny, rr, ll)), cs)
            ll = aux(l, cc + cs)
            rr = aux(r, ncc + cs)
            return merge(self.sort_tree(build(ll, cc)), self.sort_tree(build(rr, ncc)), cs)

        return DT(pre, self.sort_tree(aux(t.tree, [])))

    def filter(self, t, e, domain=None):
        """The test FILTER_A[[e]]:

          1. apply STEP_F on the defined leaves (one more execution step
             before termination);
          2. convert e into a set J of linear constraints in canonical form,
             J = α_C(FILTER_D[[e]] ⊤_D);
          3. perform tree pruning with J: J is added to the
             tree, and the parts of the tree where J does not hold become NIL.

        Conjunctions and disjunctions are handled with the meet ⋏_A and the
        approximation join ⋎_A of the filtered trees."""
        F = self.F
        pre = domain
        post = t.domain

        def step(f):
            return F.filter(f, e)

        if isinstance(e, Maybe) or (isinstance(e, BConst) and e.value):
            return DT(pre, self.prune(t.tree, [], pre, step))
        if isinstance(e, BConst):
            return DT(pre, None)
        if isinstance(e, Not):
            return self.filter(t, negate_bexp(e.expr), pre)
        if isinstance(e, BoolOp):
            t1 = self.filter(t, e.left, pre)
            t2 = self.filter(t, e.right, pre)
            if e.op == 'and':
                return self.meet(APPROXIMATION, t1, t2)
            return self.join(APPROXIMATION, t1, t2)
        if isinstance(e, Compare):
            bp = self.inner([]) if post is None else self.inner([]).meet(post)
            bs = [(c, negate(c)) for c in bp.filter(e).constraints()]
            bs.sort(key=lambda p: lkey(*p))
            return DT(pre, self.prune(t.tree, bs, pre, step))
        raise TypeError(e)

    def prune(self, t, bs, domain=None, leaf=None):
        """Tree pruning: adds the set J = bs of linear constraints (pairs
        (c, ¬c), sorted with respect to ≤_C) to the tree t; the parts of the
        tree where J does not hold become NIL. The function `leaf` is applied
        to the leaves that are kept (STEP_F for FILTER_A)."""
        pre = domain

        def split(t, bs, cs, bcs):
            # case 2 of tree pruning: the root c of t comes before min J
            # (2a: c is redundant, 2c: c is kept)
            c, nc = t.c, t.nc
            if bcs.is_leq(self.inner([c])):
                return aux(t.l, bs, cs)
            l = aux(t.l, bs, [c] + cs)
            r = aux(t.r, bs, [nc] + cs)
            if l is None and r is None:
                return None
            if l is None and isinstance(r, Node) and r.l is None:
                return r
            return Node(c, nc, l, r)

        def aux(t, bs, cs):
            # tree pruning of t with the (sorted) constraints bs = J
            bcs = self.dom(cs, pre)
            if not bs:
                # base case J = ∅: STEP_F on the leaves, and removal of the
                # nodes that became redundant
                if t is None:
                    return None
                if isinstance(t, Leaf):
                    return t if leaf is None else Leaf(leaf(t.f))
                return split(t, bs, cs, bcs)
            x, nx = bs[0]  # min J
            xs = bs[1:]
            bx = self.inner([x])
            if bcs.is_leq(bx):  # min J is redundant
                return aux(t, xs, cs)
            if bx.meet(bcs).is_bot():  # ¬min J is redundant: this part becomes NIL
                return None
            # min J is added to the tree; the side where it does not hold is NIL
            if nx <= x:  # x is normalized
                if isinstance(t, Node) and t.c == x:
                    l = aux(t.l, xs, [t.c] + cs)
                    return None if l is None else Node(t.c, t.nc, l, None)
                if isinstance(t, Node) and t.c <= x:
                    return split(t, bs, cs, bcs)
                l = aux(t, xs, [x] + cs)
                return None if l is None else Node(x, nx, l, None)
            if isinstance(t, Node) and t.c == nx:
                r = aux(t.r, xs, [t.nc] + cs)
                return None if r is None else Node(t.c, t.nc, None, r)
            if isinstance(t, Node) and t.c <= nx:
                return split(t, bs, cs, bcs)
            r = aux(t, xs, [x] + cs)
            return None if r is None else Node(nx, x, None, r)

        return aux(t, bs, [])

    def defined(self, t, condition=None):
        """Whether the ranking function is defined on all the states that
        satisfy the condition (the precondition), i.e., whether
        I ⊆ dom(γ_A(t)): then the program definitely terminates from I
        (soundness corollary)."""
        F = self.F
        domain = t.domain

        def aux(t, cs):
            if t is None:
                if condition is None:
                    return self.dom(cs, domain).is_bot()
                return True
            if isinstance(t, Leaf):
                return F.defined(t.f) or self.dom(cs, domain).is_bot()
            return aux(t.l, [t.c] + cs) and aux(t.r, [t.nc] + cs)

        if condition is not None:
            # the NIL leaves of t (no information) become undefined (⊥_F),
            # then t is filtered with the condition: the parts of t that do
            # not satisfy the condition become NIL, and are ignored below
            bot_leaf = Leaf(F.bot())

            def fill(t):
                if t is None:
                    return bot_leaf
                if isinstance(t, Node):
                    return Node(t.c, t.nc, fill(t.l), fill(t.r))
                return t

            t = self.filter(DT(t.domain, fill(t.tree)), condition)
            domain = t.domain
        return aux(t.tree, [])

    def refine(self, t, b):
        """Restricts the tree to the states in b (option -refine)."""
        return DT(b, t.tree)

    # printing

    def partitions(self, t):
        """The (non-empty) partitions of a tree with the corresponding leaves."""
        out = []

        def aux(tree, cs):
            if isinstance(tree, Node):
                aux(tree.r, [tree.nc] + cs)
                aux(tree.l, [tree.c] + cs)
                return
            b = self.dom(cs, t.domain)
            if not b.is_bot():
                out.append((b, None if tree is None else tree.f))

        aux(t.tree, [])
        return out

    def to_str(self, t):
        lines = []
        for b, f in self.partitions(t):
            lines.append('%s ? %s' % (b, 'NIL' if f is None else self.F.to_str(f)))
        return '\n'.join(lines)

    def tree_str(self, t, ind=''):
        names = self.env.vars
        if t is None:
            return '\n%sNIL' % ind
        if isinstance(t, Leaf):
            return '\n%sLEAF %s' % (ind, self.F.to_str(t.f))
        return '\n%sNODE %s%s%s' % (ind, constraint_str(t.c, names),
                                    self.tree_str(t.l, ind + '  '), self.tree_str(t.r, ind + '  '))
