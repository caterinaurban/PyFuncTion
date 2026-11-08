"""
Regression tests: Python versions of the programs in tests/termination of the
OCaml FuncTion, analyzed with the options used in its termination.sh (given in
the `# expected:` header line). Each `# expected:` line of a program is a
test, with its options; termination must be proven, unless the line is
`# expected UNKNOWN:` (as in tests/test_ctl.py). A program without such a
line is a test with the default options, where termination must be proven.

    python3 -m unittest -v
"""

import glob
import os
import re
import shlex
import unittest

from pyfunction.frontend import parse_program
from pyfunction.termination import TerminationAnalysis

HERE = os.path.dirname(os.path.abspath(__file__))
_LINE = re.compile(r'^# expected(?:( UNKNOWN)(?::(.*)|[ \t]*$)|:(.*))$', re.M)  # `# expected UNKNOWN` alone, or with `: options`
_BAD = re.compile(r'^# expected UNKNOWN[ \t]+\S.*$', re.M)


def _lines(source):
    """[(options text, expected result)] for the `# expected` lines."""
    bad = _BAD.search(source)
    if bad:
        raise ValueError('options need a colon: %r (# expected UNKNOWN: options)' % bad.group(0))
    return [((m.group(2) if m.group(1) else m.group(3)) or '', m.group(1) is None) for m in _LINE.finditer(source)]


def _options(text):
    args = shlex.split(text)
    opts = {}
    i = 0
    while i < len(args):
        a = args[i]
        if a == '-refine':
            opts['refine'] = True
            i += 1
        else:
            v = args[i + 1]
            if a == '-angelic':
                v = v.split(',')
            opts[a[1:]] = v if a in ('-domain', '-precondition', '-seed', '-angelic') else int(v)
            i += 2
    return opts


def cases(source):
    """[(options, expected result)] for the `# expected` lines (one test with
    the default options, expected to be proven, if there is none)."""
    out = [(_options(text), exp) for text, exp in _lines(source)]
    return out or [({}, True)]


def options(source):
    """The options of the first `# expected` line."""
    return cases(source)[0][0]


def analyze(path, opts=None, **kw):
    with open(path) as f:
        source = f.read()
    opts = dict(options(source) if opts is None else opts)
    opts.update(kw)
    program, fe = parse_program(source, filename=path)
    pre = opts.pop('precondition', None)
    pre = fe.condition(pre, program) if pre else None
    seed = opts.pop('seed', None)
    seeds = [fe.condition(seed, program)] if seed else []
    return TerminationAnalysis(program, seeds=seeds, **opts).run(pre)


class TerminationTests(unittest.TestCase):
    pass


def _make(path, opts, exp):
    def test(self):
        self.assertEqual(analyze(path, opts), exp, 'unexpected result for %s %s' % (os.path.basename(path), opts))
    return test


for _d in ('termination', 'python', 'issues', 'angelic'):
    for _p in sorted(glob.glob(os.path.join(HERE, _d, '*.py'))):
        with open(_p) as _f:
            _cs = cases(_f.read())
        _n = 'test_%s_%s' % (_d, os.path.splitext(os.path.basename(_p))[0])
        for _k, (_o, _e) in enumerate(_cs):
            setattr(TerminationTests, _n if len(_cs) == 1 else '%s_%d' % (_n, _k + 1), _make(_p, _o, _e))


if __name__ == '__main__':
    unittest.main()
