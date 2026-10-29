"""
Regression tests: Python versions of the programs in tests/termination of the
OCaml FuncTion, analyzed with the options used in its termination.sh (given in
the `# expected:` header line).
Termination is expected to be proven, unless a `# result: UNKNOWN` line says
otherwise.

    python3 -m unittest discover -s tests -v
"""

import glob
import os
import shlex
import unittest

from pyfunction.frontend import parse_program
from pyfunction.termination import TerminationAnalysis

HERE = os.path.dirname(os.path.abspath(__file__))


def options(source):
    opts = {}
    for line in source.splitlines():
        if line.startswith('# expected:'):
            args = shlex.split(line[len('# expected:'):])
            i = 0
            while i < len(args):
                a = args[i]
                if a == '-refine':
                    opts['refine'] = True
                    i += 1
                else:
                    v = args[i + 1]
                    opts[a[1:]] = v if a in ('-domain', '-precondition') else int(v)
                    i += 2
    return opts


def expected(source):
    return '# result: UNKNOWN' not in source


def analyze(path, **kw):
    with open(path) as f:
        source = f.read()
    opts = options(source)
    opts.update(kw)
    program, fe = parse_program(source, filename=path)
    pre = opts.pop('precondition', None)
    pre = fe.condition(pre, program) if pre else None
    return TerminationAnalysis(program, **opts).run(pre)


class TerminationTests(unittest.TestCase):
    pass


def _make(path):
    def test(self):
        with open(path) as f:
            exp = expected(f.read())
        self.assertEqual(analyze(path), exp, 'unexpected result for %s' % os.path.basename(path))
    return test


for _d in ('termination', 'python'):
    for _p in sorted(glob.glob(os.path.join(HERE, _d, '*.py'))):
        _n = 'test_%s_%s' % (_d, os.path.splitext(os.path.basename(_p))[0])
        setattr(TerminationTests, _n, _make(_p))


if __name__ == '__main__':
    unittest.main()
