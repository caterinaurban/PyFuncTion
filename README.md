# PyFuncTion

A Python port of the **termination** and **CTL** analyses of
[FuncTion](https://github.com/caterinaurban/function), for numerical Python
programs. It has no dependency outside the Python standard library: APRON is
replaced by an exact polyhedra library (double description method over Python
integers) in `pyfunction/polyhedra.py`.

As in FuncTion, a forward reachability analysis is followed by a backward
analysis that infers a piecewise-defined ranking function (a decision tree with
affine or ordinal-valued leaves) and a sufficient precondition for termination.
The analyzer answers `TRUE` when it proves termination, and `UNKNOWN` otherwise.
With `-ctl`, it proves a CTL property instead (see CTL properties below).

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
    -seed "x >= 0 and x - y >= 1"      split the decision trees on these constraints from the
                                       start: the domain widening never removes them (each
                                       comparison is a seed; the option can be repeated)
    -ctl "AG{AF{x == 0}}"              prove a CTL property instead of termination
    -ctl_existential_equivalence       CTL: prove EF, EG, EX as NOT AG NOT, NOT AF NOT, NOT AX NOT
    -angelic d,s                       the non-deterministic values of these variables are
                                       picked by the program (see Termination resilience below;
                                       the option can be repeated)
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

## Termination resilience

By default every non-deterministic value is chosen by the environment
(*demonic* non-determinism): termination is proven only if the program
terminates whatever the values are. With `-angelic`, the values assigned to the
listed variables are instead picked by the program (*angelic*
non-determinism): it is enough that some value leads to termination. This
follows the trusted non-determinism of the VMCAI 2026 paper on termination
resilience, in a preliminary version:

    $ cat resilient.py
    import random

    def main(x):
        while x > 0:
            d = random.randint(-1, 1)
            x = x - d

    $ python3 -m pyfunction resilient.py -domain octagons -minimal
    Analysis Result: UNKNOWN
    $ python3 -m pyfunction resilient.py -domain octagons -angelic d -minimal
    Analysis Result: TRUE

(The program terminates if it always picks `d = 1`, but not if `d` can be
`0` or `-1` forever.)

- Trust is declared per variable, not per expression as in the paper. An
  assignment is angelic only if its target is listed and its right-hand side
  is a whole non-deterministic value: `x = input()`, `x =
  random.randint(a, b)` (with linear bounds), and so on. Everything else stays
  demonic, e.g. `x = y + random.randint(0, 5)`.
- The parameters of the analyzed function are always demonic: naming one is
  an error.
- Values that only approximate what the program computes (`a ** b`, calls to
  unknown functions) are never a choice: they stay demonic even when assigned
  to an angelic variable.
- The angelic assignment fixes three cases where the operator of the paper is
  unsound: it projects the whole path of each leaf instead of each decision
  node separately, and drops a leaf when the projection is not exact over the
  integers or cannot be represented by the abstract domain (the leaf is then
  undefined, which is sound). The differences are listed in the docstring of
  `DecisionTree.bwd_assign_angelic`, and `tests/angelic` has an example for
  each.
- The usual limits of the loop analysis remain: e.g. a loop whose step is a
  variable (`z = z + c`) is only proven when `-refine` gives the step's value.

## CTL properties

With `-ctl`, the analyzer proves a CTL property, written as in FuncTion
(the AST version of its CTL analysis, `main/CTLIterator.ml`):

    p ::= cond | label: cond
        | AX{p} | AF{p} | AG{p} | AU{p}{p}
        | EX{p} | EF{p} | EG{p} | EU{p}{p}
        | AND{p}{p} | OR{p}{p} | NOT{p}

The atoms are Python conditions over the program variables (FuncTion's `&&`,
`||`, `!`, `true` are accepted too). `label: cond` holds only at the program
points marked by a `#LABEL: label` comment, which is a no-op statement where
it is written: on its own line, it belongs to the block given by its
indentation; at the end of a statement, it comes after the statement.

    $ cat tests/ctl/potential_termination_1.py
    def main():
        y = 1
        i = int(input())
        x = int(input())
        if i > 10:
            x = 1
        while x == y:
            pass
        #LABEL: exit

    $ python3 -m pyfunction tests/ctl/potential_termination_1.py -domain polyhedra -ctl "EF{exit: true}" -minimal
    Analysis Result: TRUE
    $ python3 -m pyfunction tests/ctl/potential_termination_1.py -domain polyhedra -ctl "AF{exit: true}" -minimal
    Analysis Result: UNKNOWN

As in FuncTion, the analysis computes a decision tree for each subformula at
each label (defined on states satisfying it, and bounding the steps before
it holds for F and U), by least fixpoints for F and U and greatest fixpoints
(with a dual widening) for G; the property is proven if the tree at the entry
is defined on the precondition. Also as in FuncTion, the program exits have
no successor: a finite path never satisfies AG/EG, so a program that should
satisfy AG p must not terminate (e.g. `while True: pass` at the end).

Non-determinism, and `-angelic`:

- under the universal operators (AX, AF, AG, AU) the choices are demonic,
  except for the variables listed in `-angelic`, which are angelic as for
  termination;
- under the existential operators (EX, EF, EG, EU) the path is existential,
  so every choice (`x = input()`, `x = random.randint(a, b)`) is angelic,
  whatever `-angelic` lists;
- values that only approximate the program (`a ** b`, calls to unknown
  functions, `%` by a variable) are demonic everywhere.

Differences with FuncTion:

- FuncTion makes the existential properties undefined after a
  non-deterministic assignment (its tests `potential_termination_1.c` and
  `Bangalore` are marked as unsupported); here these choices are angelic;
- the existential operators and the atoms need filters that under-approximate
  the conditions: FuncTion supports them with polyhedra only, here any domain
  works, but a comparison that the domain does not represent exactly (e.g.
  `x < y` with boxes) or that is not linear is taken as false;
- choices inside conditions are first assigned to temporaries, so that
  `5 < random.randint(0, 10) < 3` compares one value (an angelic choice must
  be the same in both comparisons); `if random.randint(0, 1):` is a coin flip;
- there is no automatic `exit` label: mark the exits with `#LABEL:`;
- AG/EG also check the property at the `#LABEL` points, AX/EX handle
  `assume` and program exits (FuncTion skips them);
- the CTL analysis of FuncTion's control-flow graphs (`-ctl-cfg`), with
  function calls and `break`/`continue`, is not ported.

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
  integer); `assume(cond)` restricts the analyzed executions. All of them are
  demonic, unless the variable they are assigned to is listed in `-angelic`
- `#LABEL: name` comments (for the CTL properties)

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
      ctl.py             CTL properties and iterator (frontend/CTLProperty.ml, main/CTLIterator.ml)
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

The options of the command line are in the panel below the program, including
`-angelic` (the "angelic" field) and `-ctl` (the "property" field: empty for
termination). For a CTL property, the replay goes through the subformulas in
the order they are computed, and the "subformula" menu below the labeled
program selects the tree shown when clicking a label.

## Tests

    python3 -m unittest -v

`tests/termination` contains Python versions of the C programs in
[`tests/termination`](https://github.com/caterinaurban/function/tree/master/tests/termination)
of FuncTion, analyzed with the options used in its `termination.sh`
(`# expected:` header line); `tests/python` contains programs using
Python-specific constructs. `tests/issues` collects problems that have been
fixed: each program comes with a `.txt` file describing the issue.
`tests/angelic` contains programs for `-angelic`, in particular the cases
where the operator of the VMCAI 2026 paper is unsound (the comment at the top of
each file explains it). `tests/ctl` contains Python versions of the CTL
tests of FuncTion (`tests/CTLTest.ml`, AST analysis), with one `# expected:`
line per property (`# expected UNKNOWN:` when it is not proven; run by
`tests/test_ctl.py`). The test suite and the examples of the graphical
interface include all five folders.

See `NOTES.md` for the differences with the OCaml version, and for per-file
notes with suggestions for improving the analysis.

## License and credits

PyFuncTion is released under the MIT License (see `LICENSE`).

It is a Python port of the termination analysis of
[FuncTion](https://github.com/caterinaurban/function), by Caterina Urban,
with contributions by Nathanaël Courant (precise widening operators) and
Samuel Ueltschi.
