# X0 exact checks

This one-shot instrument checks small ordinary rooted agreement forests. It
enumerates label partitions, compares induced rooted cluster families, checks
explicit vertex spans, and records minimum refining partitions for a current
forest. It also constructs the actual two-pendant-cut children from literal
receipt inputs and performs singleton deletion and common-cherry contraction
with reconstruction data.

Use it for adversarial replay of this algorithm target. The existing project
oracles are development instruments; this implementation deliberately imports
none of their routines. The BootLoops toolkit index contains no rooted-MAF
instrument. This separate implementation is required by the independent X0
assignment and is not registered as a replacement for the existing oracles.

The integer `components` is the number of forest blocks. The current-state
optimum is `components - current_forest_block_count` further cuts. Initial
tree-tree cuts are `components - 1`; empty states have zero components.
Tree inputs use distinct integer labels and nested binary pairs. No rho label
is introduced. Address strings identify original vertices, with the empty
string denoting the root. A failure raises an exception and produces a
nonzero exit; PASS is printed only after every asserted comparison executes.

Run the known-answer and corruption controls before the retained inputs:

```sh
./bootloops-python research/rmaf/algorithm/x0/run_x0.py --stage controls
./bootloops-python research/rmaf/algorithm/x0/run_x0.py --stage pilot
./bootloops-python research/rmaf/algorithm/x0/run_x0.py --stage bounded
./bootloops-python research/rmaf/algorithm/x0/source_controls.py
```

Original execution records live under `results/algorithm-x0-*-v1.json` and
matching `.log` files. Replay writes to these paths; preserve originals before
running again. The source-predicate controls were frozen after the bounded
run and are explicitly labelled supplementary. Read `REPORT.md` for the
measured results and the limits of these checks.

The checks count as finite evidence after the 24 plants and corruptions pass,
the false optimum comparator fires, the source predicates pass their five
supplementary controls, and literal receipt hashes match. A complete algorithm
claim still requires universal coverage, complexity, nonauthor reconstruction,
and formal verification at the consuming hypotheses. None is supplied here.
