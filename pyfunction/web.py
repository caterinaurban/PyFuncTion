"""
The bridge between the graphical interface (gui.html, served by gui.py) and
the analysis: the page calls the functions below, which exchange JSON strings.

The backward analysis is recorded step by step (TerminationAnalysis(record=...)):
each statement, each iteration of the loops, and each step of the widening,
so that the interface can replay it.

Run the interface with:

    python -m pyfunction.gui
"""

import glob
import json
import os
import re
from fractions import Fraction

from .decision_tree import Node, Leaf
from .frontend import parse_program, UnsupportedError
from .functions import Aff, Ord, FUN, BOT, TOP
from .linear import canonical_str
from .syntax import Assign, Assume, If, While, Return, aexp_str, bexp_str, program_str
from .termination import TerminationAnalysis, Timeout

MAX_EVENTS = 20000

_session = {}


def _lbl(l):
    return 'ℓ%d' % l


def _stmt_title(s):
    if isinstance(s, Assign):
        return 'ASSIGN←_A[[%s ← %s]]' % (s.target, aexp_str(s.value))
    if isinstance(s, Assume):
        return 'FILTER_A[[%s]] (assume)' % bexp_str(s.cond)
    if isinstance(s, Return):
        return 'program exit: λ. 0'
    if isinstance(s, If):
        return 'if %s: FILTER_A[[%s]](then) ⋎_A FILTER_A[[not %s]](else)' % ((bexp_str(s.cond),) * 3)
    if isinstance(s, While):
        return 'while %s: loop done (fixpoint at %s)' % (bexp_str(s.cond), _lbl(s.label))
    return type(s).__name__


_WIDEN = {
    'widen_t1': 'widening: t1, the previous iterate',
    'widen_t2': 'widening: t2, the current iterate',
    'widen_right': 'widening: check for cases A, B and C (wrong predictions become ⊤)',
    'left_unification': 'widening: domain widening (left unification)',
    'widen_up': 'widening: leaf widening ▿_F',
    'widen_leaves': 'widening: value widening ▾_F (the new iterate)',
}


class _Recorder:
    """Collects the steps of the backward analysis, with their context (the
    enclosing loops and iterations)."""

    def __init__(self):
        self.events = []
        self.trees = []
        self.loops = []  # [(loop label, iteration)]
        self.truncated = False

    def context(self):
        return ' › '.join('loop %s' % _lbl(l) + (', iteration %d' % n if n else '') for l, n in self.loops)

    def __call__(self, kind, label, tree, **info):
        if kind == 'exit':
            self.loops.append((label, 0))
        elif kind == 'iteration':
            self.loops[-1] = (label, info['n'])
        if label is None:  # the steps of the widening, in the innermost loop
            label = self.loops[-1][0] if self.loops else None
        if kind == 'label':
            s = info.get('stmt')
            title = '%s: %s' % (_lbl(label), _stmt_title(s) if s is not None else 'end of block')
        elif kind == 'exit':
            title = '%s: loop exit, FILTER_A[[not condition]](t)' % _lbl(label)
        elif kind == 'iteration':
            n = info['n']
            if n == 1:
                title = '%s: iterate 1 = ⊥ (start%s)' % (_lbl(label), ', split on the seeds' if info.get('seeded') else '')
            else:
                title = '%s: iterate %d%s' % (_lbl(label), n, ' (after widening)' if info.get('widened') else '')
        elif kind == 'body':
            title = '%s: iteration %d, FILTER_A[[condition]](body)' % (_lbl(label), info['n'])
        elif kind == 'join':
            title = '%s: iteration %d, F(i) = body ⋎_A exit' % (_lbl(label), info['n'])
        elif kind == 'fixpoint':
            title = '%s: fixpoint, after %d iterations' % (_lbl(label), info['n'])
        else:
            title = '%s: %s' % (_lbl(label) if label is not None else '', _WIDEN.get(kind, kind))
        ctx = self.context()
        if kind == 'fixpoint':
            self.loops.pop()
        if len(self.events) >= MAX_EVENTS:
            self.truncated = True
            return
        self.events.append({'kind': kind, 'label': label, 'title': title, 'context': ctx,
                            'depth': len(self.loops) + (1 if kind == 'fixpoint' else 0)})
        self.trees.append(tree)


def _options(opts):
    o = {}
    if opts.get('domain'):
        o['domain'] = opts['domain']
    if opts.get('ordinals') not in (None, '', 'none'):
        o['ordinals'] = int(opts['ordinals'])
    for k in ('joinbwd', 'joinfwd', 'retrybwd'):
        if opts.get(k) not in (None, ''):
            o[k] = int(opts[k])
    o['refine'] = bool(opts.get('refine'))
    o['timeout'] = float(opts.get('timeout') or 30)
    return o


def analyze(source, opts_json='{}'):
    """Runs the analysis; returns the program, the result and the list of
    recorded steps (their trees are fetched with view())."""
    opts = json.loads(opts_json)
    _session.clear()
    try:
        program, fe = parse_program(source, opts.get('main') or 'main')
        pre = opts.get('precondition') or None
        precondition = fe.condition(pre, program) if pre else None
        seeds = [fe.condition(opts['seed'], program)] if opts.get('seed') else []
    except UnsupportedError as e:
        return json.dumps({'error': 'Unsupported program: %s' % e})
    except Exception as e:  # e.g. syntax errors in the precondition
        return json.dumps({'error': '%s: %s' % (type(e).__name__, e)})
    rec = _Recorder()
    try:
        a = TerminationAnalysis(program, record=rec, seeds=seeds, **_options(opts))
    except ValueError as e:  # e.g. a non-linear seed
        return json.dumps({'error': 'Unsupported option: %s' % e})
    try:
        r = a.run(precondition)
        result = 'TRUE' if r else 'UNKNOWN'
    except Timeout:
        result = 'TIMEOUT'
    except RecursionError:
        return json.dumps({'error': 'the analysis exceeded the recursion limit'})
    _session.update(analysis=a, recorder=rec, program=program)
    lines = []
    for text in program_str(program).split('\n'):
        labels = [int(x) for x in re.findall(r'\[\s*(\d+):\]', text)]
        lines.append({'text': text, 'labels': labels})
    return json.dumps({
        'result': result,
        'variables': list(program.variables),
        'inputs': list(program.inputs),
        'program': lines,
        'labels': sorted(a.bwd),
        'forward': {l: str(b) for l, b in a.fwd.items()},
        'events': rec.events,
        'truncated': rec.truncated,
        'warnings': fe.warnings,
    })


def _fl(x):
    return float(x)


def _region(b, env, axes, slice_, window):
    """The part of the partition b in the plotting window: [lo, hi] for one
    axis, the vertices of a polygon for two (the other variables are fixed
    to their value in slice_)."""
    if b.is_bot():
        return None
    n = env.n
    idx = [env.index[v] for v in axes]

    def unit(i, a, c):
        return tuple(a if j == i else 0 for j in range(n)) + (c,)

    eqs = [unit(i, 1, -int(slice_.get(v, 0))) for v, i in env.index.items() if i not in idx]
    ineqs = []
    for k, i in enumerate(idx):
        lo, hi = window[2 * k], window[2 * k + 1]
        ineqs.append(unit(i, 1, -int(lo)))
        ineqs.append(unit(i, -1, int(hi)))
    P = b.to_poly().meet_constraints(eqs, ineqs)
    if P.empty:
        return None
    pts = [tuple(Fraction(r[i], r[-1]) for i in idx) for r in P.rays if r[-1] > 0]
    if len(idx) == 1:
        return [_fl(min(p[0] for p in pts)), _fl(max(p[0] for p in pts))]
    pts = sorted(set(pts))
    cx = sum(p[0] for p in pts) / len(pts)
    cy = sum(p[1] for p in pts) / len(pts)
    from math import atan2
    pts.sort(key=lambda p: atan2(_fl(p[1] - cy), _fl(p[0] - cx)))
    return [[_fl(x), _fl(y)] for x, y in pts]


def _leaf_info(D, f, env, axes, slice_):
    F = D.F
    if f is None:
        return {'kind': 'nil', 'f': 'NIL'}
    s = F.to_str(f)
    a = f
    if isinstance(f, Ord):
        if any(F.F.defined(c) and (any(c.coeffs) or c.const) for c in f.ff):
            return {'kind': 'ord', 'f': s}
        a = f.f
    if a.kind == BOT:
        return {'kind': 'bot', 'f': s}
    if a.kind == TOP:
        return {'kind': 'top', 'f': s}
    # the affine function restricted to the plotted axes
    const = a.const + sum(a.coeffs[i] * int(slice_.get(v, 0)) for v, i in env.index.items() if v not in axes)
    return {'kind': 'fun', 'f': s, 'coeffs': [_fl(a.coeffs[env.index[v]]) for v in axes], 'const': _fl(const)}


def view(which, ident, plot_json='{}'):
    """A tree (an event of the replay, or the final tree at a label), with
    its leaves and their partitions; plot = {axes, slice, window}."""
    a = _session.get('analysis')
    if a is None:
        return json.dumps({'error': 'no analysis'})
    if which == 'event':
        t = _session['recorder'].trees[int(ident)]
    else:
        t = a.bwd[int(ident)]
    D, env = a.D, a.env
    plot = json.loads(plot_json)
    axes = [v for v in plot.get('axes', []) if v in env.index]
    slice_ = plot.get('slice', {})
    window = plot.get('window', [-10, 10, -10, 10])
    leaves = []

    def aux(tree, cs):
        if isinstance(tree, Node):
            return {'c': canonical_str(tree.c, env.vars),
                    'l': aux(tree.l, [tree.c] + cs), 'r': aux(tree.r, [tree.nc] + cs)}
        b = D.dom(cs, t.domain)
        info = _leaf_info(D, None if tree is None else tree.f, env, axes, slice_)
        info['id'] = len(leaves)
        info['empty'] = b.is_bot()
        info['partition'] = str(b)
        info['region'] = _region(b, env, axes, slice_, window) if axes and not info['empty'] else None
        leaves.append(info)
        return {'leaf': info['id']}

    tree = aux(t.tree, [])
    return json.dumps({'tree': tree, 'leaves': leaves,
                       'domain': None if t.domain is None else str(t.domain)})


def page():
    """The page of the interface (gui.html), with the examples embedded."""
    here = os.path.dirname(os.path.abspath(__file__))
    root = os.path.dirname(here)
    with open(os.path.join(here, 'gui.html'), encoding='utf-8') as f:
        text = f.read()
    examples = []
    for d in ('termination', 'python', 'issues'):
        for p in sorted(glob.glob(os.path.join(root, 'tests', d, '*.py'))):
            with open(p, encoding='utf-8') as f:
                source = f.read()
                examples.append({'name': '%s/%s' % (d, os.path.basename(p)), 'source': source})
    text = text.replace('/*EXAMPLES*/[]', json.dumps(examples).replace('</', '<\\/'), 1)
    return ('<!doctype html>\n<html lang="en">\n<head>\n<meta charset="utf-8">\n'
            '<meta name="viewport" content="width=device-width, initial-scale=1">\n'
            '<style>body { margin: 0; } [hidden] { display: none !important; }</style>\n'
            + text.replace('<div class="app">', '</head>\n<body>\n<div class="app">', 1) + '\n</body>\n</html>\n')
