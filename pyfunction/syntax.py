"""
Abstract syntax of the analyzed programs (cf. frontend/AbstractSyntax.ml).

The language is:

    expr ::= X | c | [c1, c2] | -expr | expr ⋄ expr
    stmt ::= ℓ X ← expr
           | if ℓ expr ⋈ 0 then stmt end
           | while ℓ expr ⋈ 0 do stmt done
           | stmt; stmt

extended with else branches, boolean combinations of comparisons (and, or,
not), `assume` and program exits (Return). Expressions have no side effects
(function calls are inlined by the frontend), and all variables are integers.

Each statement is labeled with a program point ℓ ∈ L (an integer); the
analysis computes one abstract element per label: the forward invariant and
the ranking function.
"""

from dataclasses import dataclass, field
from typing import List, Optional, Tuple, Union


# arithmetic expressions

@dataclass(frozen=True)
class Var:
    name: str


@dataclass(frozen=True)
class Const:
    value: int


@dataclass(frozen=True)
class Random:
    """A non-deterministic integer: [-∞, +∞]."""


@dataclass(frozen=True)
class Interval:
    """A non-deterministic integer in [lo, hi] (the input [c1, c2] of the
    grammar); the bounds are arithmetic expressions, or None for infinity."""
    lo: Optional['AExp']
    hi: Optional['AExp']


@dataclass(frozen=True)
class Neg:
    expr: 'AExp'


@dataclass(frozen=True)
class BinOp:
    op: str  # one of + - * // %
    left: 'AExp'
    right: 'AExp'


AExp = Union[Var, Const, Random, Interval, Neg, BinOp]

_aprec = {'+': 5, '-': 5, '*': 6, '//': 6, '%': 6}


def aexp_prec(e):
    if isinstance(e, BinOp):
        return _aprec[e.op]
    if isinstance(e, Neg):
        return 99
    return 100


def aexp_str(e):
    if isinstance(e, Var):
        return e.name
    if isinstance(e, Const):
        return str(e.value)
    if isinstance(e, Random):
        return '?'
    if isinstance(e, Interval):
        lo = '-oo' if e.lo is None else aexp_str(e.lo)
        hi = '+oo' if e.hi is None else aexp_str(e.hi)
        return '[%s, %s]' % (lo, hi)
    if isinstance(e, Neg):
        s = aexp_str(e.expr)
        return '-(%s)' % s if aexp_prec(e.expr) <= aexp_prec(e) else '-' + s
    if isinstance(e, BinOp):
        l, r = aexp_str(e.left), aexp_str(e.right)
        if aexp_prec(e.left) < aexp_prec(e):
            l = '(%s)' % l
        if aexp_prec(e.right) <= aexp_prec(e):
            r = '(%s)' % r
        return '%s %s %s' % (l, e.op, r)
    raise TypeError(e)


# boolean expressions

@dataclass(frozen=True)
class BConst:
    value: bool


@dataclass(frozen=True)
class Maybe:
    """A non-deterministic boolean."""


@dataclass(frozen=True)
class Not:
    expr: 'BExp'


@dataclass(frozen=True)
class BoolOp:
    op: str  # and | or
    left: 'BExp'
    right: 'BExp'


@dataclass(frozen=True)
class Compare:
    op: str  # one of < <= > >=
    left: AExp
    right: AExp


BExp = Union[BConst, Maybe, Not, BoolOp, Compare]

_neg_cmp = {'<': '>=', '<=': '>', '>': '<=', '>=': '<'}


def negate(b):
    """Negation of a boolean expression, pushed down to the comparisons
    (used for the else branch and the loop exit: e ⋈̸ 0)."""
    if isinstance(b, BConst):
        return BConst(not b.value)
    if isinstance(b, Maybe):
        return b
    if isinstance(b, Not):
        return b.expr
    if isinstance(b, BoolOp):
        return BoolOp('or' if b.op == 'and' else 'and', negate(b.left), negate(b.right))
    if isinstance(b, Compare):
        return Compare(_neg_cmp[b.op], b.left, b.right)
    raise TypeError(b)


def bexp_prec(b):
    if isinstance(b, BoolOp):
        return 2 if b.op == 'and' else 1
    if isinstance(b, Compare):
        return 4
    if isinstance(b, Not):
        return 99
    return 100


def bexp_str(b):
    if isinstance(b, BConst):
        return 'True' if b.value else 'False'
    if isinstance(b, Maybe):
        return '?'
    if isinstance(b, Not):
        s = bexp_str(b.expr)
        return 'not (%s)' % s if bexp_prec(b.expr) <= bexp_prec(b) else 'not ' + s
    if isinstance(b, BoolOp):
        l, r = bexp_str(b.left), bexp_str(b.right)
        if bexp_prec(b.left) < bexp_prec(b):
            l = '(%s)' % l
        if bexp_prec(b.right) <= bexp_prec(b):
            r = '(%s)' % r
        return '%s %s %s' % (l, b.op, r)
    if isinstance(b, Compare):
        return '%s %s %s' % (aexp_str(b.left), b.op, aexp_str(b.right))
    raise TypeError(b)


# statements

@dataclass
class Assign:
    """X ← expr"""
    target: str
    value: AExp


@dataclass
class Assume:
    """Only the executions satisfying the condition go on."""
    cond: BExp


@dataclass
class If:
    """if cond then then else orelse end"""
    cond: BExp
    then: 'Block'
    orelse: 'Block'


@dataclass
class While:
    """while ℓ cond do body done; ℓ (`label`) is the loop head, where the
    loop invariant and the ranking function of the loop are recorded."""
    cond: BExp
    body: 'Block'
    label: int = -1


@dataclass
class Return:
    """Program exit."""


Stmt = Union[Assign, Assume, If, While, Return]


@dataclass
class Block:
    """A sequence of labeled statements followed by an exit label."""
    stmts: List[Tuple[int, Stmt]] = field(default_factory=list)
    end: int = -1


@dataclass
class Program:
    variables: List[str]  # all program variables, in a fixed order
    inputs: List[str]  # the parameters of the analyzed function
    body: Block


def label_program(stmts):
    """Builds a labeled block from a list of statements (cf. ItoA.label_block):
    each statement gets the label of the program point before it, each block
    a label for the program point after its last statement."""
    counter = [0]

    def new():
        counter[0] += 1
        return counter[0]

    def label_stmt(s):
        if isinstance(s, If):
            then = label_block(s.then)
            return If(s.cond, then, label_block(s.orelse))
        if isinstance(s, While):
            label = new()
            return While(s.cond, label_block(s.body), label)
        return s

    def label_block(ss):
        out = []
        for s in ss:
            l = new()
            out.append((l, label_stmt(s)))
        return Block(out, new())

    return label_block(stmts)


def _label_str(l):
    return '[%2d:]' % l


def block_str(b, ind=''):
    lines = []
    for l, s in b.stmts:
        lines.extend(stmt_str(l, s, ind))
    lines.append('%s%s' % (ind, _label_str(b.end)))
    return lines


def stmt_str(l, s, ind):
    pre = '%s%s ' % (ind, _label_str(l))
    if isinstance(s, Assign):
        return [pre + '%s = %s' % (s.target, aexp_str(s.value))]
    if isinstance(s, Assume):
        return [pre + 'assume %s' % bexp_str(s.cond)]
    if isinstance(s, Return):
        return [pre + 'exit']
    if isinstance(s, If):
        out = [pre + 'if %s:' % bexp_str(s.cond)]
        out.extend(block_str(s.then, ind + '    '))
        out.append('%s      else:' % ind)
        out.extend(block_str(s.orelse, ind + '    '))
        return out
    if isinstance(s, While):
        out = [pre + 'while %s %s:' % (_label_str(s.label), bexp_str(s.cond))]
        out.extend(block_str(s.body, ind + '    '))
        return out
    raise TypeError(s)


def program_str(p):
    return '\n'.join(block_str(p.body))
