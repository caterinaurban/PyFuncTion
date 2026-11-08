"""
Command line interface:

    python -m pyfunction <file.py> [options]
    python -m pyfunction <file.py> -ctl "AG{AF{x == 0}}" [options]

The analyzer performs a forward reachability analysis followed by a backward
analysis inferring a piecewise-defined ranking function and a sufficient
precondition for the program to terminate (or, with -ctl, to satisfy a CTL
property). It answers TRUE when it can prove termination (or the property)
under the given precondition, and UNKNOWN otherwise.
"""

import argparse
import sys
import time

from .frontend import parse_program, UnsupportedError
from .syntax import program_str
from .termination import TerminationAnalysis, Timeout
from .ctl import CTLAnalysis, PropertyError, parse_property, translate_property


def main(argv=None):
    ap = argparse.ArgumentParser(prog='pyfunction', description='Termination and CTL analysis of numerical Python programs.')
    ap.add_argument('file', help='Python file to analyze')
    ap.add_argument('-termination', '--termination', action='store_true', help='termination analysis (default)')
    ap.add_argument('-ctl', '--ctl', default=None, metavar='PROPERTY',
                    help='CTL analysis of the property, e.g. "AG{AF{x == 0}}" (atoms are Python conditions; '
                    '"name: cond" holds only at the #LABEL: name comments)')
    ap.add_argument('-ctl_existential_equivalence', '--ctl_existential_equivalence', action='store_true',
                    help='CTL: prove EF, EG, EX through NOT AG NOT, NOT AF NOT, NOT AX NOT')
    ap.add_argument('-main', '--main', default='main', help='analyzed function (default: main, '
                    'or the module top-level code if there is no such function)')
    ap.add_argument('-domain', '--domain', default='boxes', choices=['boxes', 'octagons', 'polyhedra'],
                    help='abstract domain for the partitions (default: boxes)')
    ap.add_argument('-ordinals', '--ordinals', type=int, default=None, metavar='N',
                    help='ordinal-valued ranking functions, up to w^N')
    ap.add_argument('-joinfwd', '--joinfwd', type=int, default=2, help='widening delay in forward analysis')
    ap.add_argument('-joinbwd', '--joinbwd', type=int, default=2, help='widening delay in backward analysis')
    ap.add_argument('-retrybwd', '--retrybwd', type=int, default=5)
    ap.add_argument('-refine', '--refine', action='store_true',
                    help='reduce the backward analysis to the reachable states')
    ap.add_argument('-precondition', '--precondition', default=None,
                    help='precondition assumed at the program entry (a Python boolean expression)')
    ap.add_argument('-seed', '--seed', action='append', default=[],
                    help='constraints to split the decision trees on from the start, e.g. "x >= 0 and x - y >= 1" '
                    '(each comparison is a seed; the domain widening never removes them; can be repeated)')
    ap.add_argument('-angelic', '--angelic', action='append', default=[], metavar='X,Y',
                    help='variables whose non-deterministic values (x = random.randint(a, b), x = input(), ...) '
                    'are picked by the program instead of the environment: termination is then proven '
                    'if some value leads to termination (parameters are always demonic; can be repeated)')
    ap.add_argument('-timeout', '--timeout', type=float, default=300.0, help='timeout in seconds')
    ap.add_argument('-minimal', '--minimal', action='store_true', help='print the analysis result only')
    ap.add_argument('-time', '--time', action='store_true', help='print the analysis time')
    ap.add_argument('-tracefwd', '--tracefwd', action='store_true')
    ap.add_argument('-tracebwd', '--tracebwd', action='store_true')
    args = ap.parse_args(argv)

    sys.setrecursionlimit(max(10000, sys.getrecursionlimit()))
    with open(args.file) as f:
        source = f.read()
    try:
        program, fe = parse_program(source, args.main, args.file)
        precondition = fe.condition(args.precondition, program) if args.precondition else None
        seeds = [fe.condition(s, program) for s in args.seed]
        prop = translate_property(parse_property(args.ctl), fe, program) if args.ctl is not None else None
    except UnsupportedError as e:
        print('Unsupported program: %s' % e, file=sys.stderr)
        return 2
    except PropertyError as e:
        print('Invalid property: %s' % e, file=sys.stderr)
        return 2
    for w in fe.warnings:
        print('Warning: %s' % w, file=sys.stderr)
    out = sys.stdout
    if not args.minimal:
        out.write('\nAbstract Syntax:\n%s\n' % program_str(program))
    kw = dict(domain=args.domain, ordinals=args.ordinals, joinfwd=args.joinfwd, joinbwd=args.joinbwd,
              refine=args.refine, retrybwd=args.retrybwd, timeout=args.timeout, tracefwd=args.tracefwd,
              tracebwd=args.tracebwd, out=out, seeds=seeds,
              angelic=[x for a in args.angelic for x in a.split(',') if x])
    try:
        if prop is None:
            analysis = TerminationAnalysis(program, **kw)
        else:
            analysis = CTLAnalysis(program, prop, existential_equivalence=args.ctl_existential_equivalence, **kw)
            for w in analysis.warnings:
                print('Warning: %s' % w, file=sys.stderr)
    except ValueError as e:  # e.g. a non-linear seed
        print('Unsupported option: %s' % e, file=sys.stderr)
        return 2
    start = time.time()
    try:
        terminating = analysis.run(precondition)
    except ValueError as e:  # e.g. EU with -ctl_existential_equivalence
        print('Unsupported option: %s' % e, file=sys.stderr)
        return 2
    except Timeout:
        out.write('\nThe Analysis Timed Out!\n\nDone.\n')
        return 1
    stop = time.time()
    if not args.minimal:
        out.write('\nForward Analysis:\n%s\n' % analysis.forward_str())
        out.write('\nBackward Analysis:\n%s\n' % analysis.backward_str())
    out.write('Analysis Result: %s\n' % ('TRUE' if terminating else 'UNKNOWN'))
    if args.time:
        out.write('Time: %f s\n' % (stop - start))
    if not args.minimal:
        out.write('\nDone.\n')
    return 0


if __name__ == '__main__':
    sys.exit(main())
