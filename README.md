# PyFuncTion

A Python port of the **termination** analysis of
[FuncTion](https://github.com/caterinaurban/function), for numerical Python
programs. It has no dependency outside the Python standard library: APRON is
replaced by an exact polyhedra library (double description method over Python
integers) in `pyfunction/polyhedra.py`.

As in FuncTion, a forward reachability analysis is followed by a backward
analysis that infers a piecewise-defined ranking function (a decision tree with
affine or ordinal-valued leaves) and a sufficient precondition for termination.
The analyzer answers `TRUE` when it proves termination, and `UNKNOWN` otherwise.

## Usage

Python 3.10 or later. From this folder:

    python3 -m pyfunction <file.py> [options]

or, after `pip install .` (or `pip install -e .` while developing), from anywhere:

    pyfunction <file.py> [options]

Options (same names as FuncTion; `--name` also works):

    -main main                         analyzed function (default: main; without
                                       such a function the module top-level code is analyzed)
    -domain boxes|octagons|polyhedra   abstract domain for the partitions (default: boxes)
    -ordinals N                        ordinal-valued ranking functions (up to w^N)
    -joinfwd 2                         widening delay in the forward analysis
    -joinbwd 2                         widening delay in the backward analysis
    -retrybwd 5
    -refine                            reduce the backward analysis to the reachable states
    -precondition "x > 0"              precondition at the entry (a Python expression)
    -timeout 300                       timeout in seconds
    -minimal                           print the analysis result only
    -time, -tracefwd, -tracebwd

Example:

    $ cat countdown.py
    def main(x):
        while x != 0:
            if x > 0:
                x = x - 1
            else:
                x = x + 1

    $ python3 -m pyfunction countdown.py -minimal
    Analysis Result: TRUE

The parameters of the analyzed function are its (unknown) inputs. Variables
that are never initialized have unknown values too.

## Supported Python subset

The frontend (`pyfunction/frontend.py`) works on the AST of the program (`ast` module):

- integer variables and literals, `True`/`False`
- `+ - * // %`, unary `- + ~`, `and or not`, comparisons (also chained),
  conditional expressions `a if c else b`
- assignments (plain, augmented, annotated, chained `a = b = e`, tuple
  `a, b = e1, e2`), `if/elif/else`, `while`, `for v in range(...)` (constant
  step), `pass`, `return`, `assert`, `raise`, `exit()`
- calls to non-recursive functions of the same module (inlined, also with
  early returns outside of loops), also through aliases (`main = f`), `abs`,
  `min`, `max`, `int`
- non-determinism: `random.randint(a, b)`, `random.randrange(a, b)`,
  `input()`, and calls to unknown functions (approximated by an arbitrary
  integer); `assume(cond)` restricts the analyzed executions

`assert`, `raise` and `exit()` terminate the program, as does `return` in the
analyzed function. Non-linear expressions are approximated by non-determinism,
except for `//` and `%` by a constant, which are encoded exactly.

Not supported yet: `break`/`continue`, loop `else`, recursion, floats, lists and
other data structures, classes, exceptions handling, `global`.

## Layout

The OCaml files in parentheses are the corresponding modules of FuncTion.

    pyfunction/
      syntax.py          abstract syntax (frontend/AbstractSyntax.ml)
      frontend.py        Python AST -> abstract syntax
      linear.py          linear constraints, linearization (utils/Constraints.ml)
      polyhedra.py       exact polyhedra (replaces APRON/NewPolka)
      partition.py       boxes, octagons, polyhedra (domains/Numerical.ml)
      functions.py       affine and ordinal-valued functions (domains/Affines.ml, domains/Ordinals.ml)
      decision_tree.py   decision trees (domains/DecisionTree.ml)
      termination.py     forward/backward iterator (main/TerminationIterator.ml)
      __main__.py        command line interface (main/Main.ml)
      gui.py, gui.html   graphical interface (see below)
      web.py             analysis recorded step by step, for the interface

## Graphical interface

From this folder (nothing to install, standard library only):

    python3 -m pyfunction.gui

starts a small web server on this machine and opens the interface in the
browser (Ctrl+C stops it; `--port N` and `--no-browser` are available). Write
or pick a program, analyze it, then:

- click a label ℓ of the labeled program to see the ranking function inferred
  there: the decision tree, the plot of the function (one or two variables,
  the others fixed to a value of your choice) and its partitions;
- replay the backward analysis step by step (buttons, slider, ← → keys, or
  play): each statement, each iteration of the loops and each step of the
  widening, with the tree and the plot at that point.

## Tests

    python3 -m unittest discover -s tests -v

`tests/termination` contains Python versions of the C programs in
[`tests/termination`](https://github.com/caterinaurban/function/tree/master/tests/termination)
of FuncTion, analyzed with the options used in its `termination.sh`
(`# expected:` header line); `tests/python` contains programs using
Python-specific constructs. `tests/issues` collects known problems: each
program comes with a `.txt` file describing the issue (these programs are not
run by the test suite).

See `NOTES.md` for the differences with the OCaml version, and for per-file
notes with suggestions for improving the analysis.

## License and credits

PyFuncTion is released under the MIT License (see `LICENSE`).

It is a Python port of the termination analysis of
[FuncTion](https://github.com/caterinaurban/function), by Caterina Urban,
with contributions by Nathanaël Courant (precise widening operators) and
Samuel Ueltschi.
