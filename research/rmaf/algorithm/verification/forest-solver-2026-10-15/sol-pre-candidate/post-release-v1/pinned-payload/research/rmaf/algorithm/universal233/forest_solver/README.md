# Generic forest solver

`GenericForest.solve` takes an optional target tree, a literal list of current source trees, and an additional cut budget. `ForestDisjoint.exact_of_ordinary` proves exact minimum correctness under the printed `OrdinaryIH` for an ordinary pair of trees. The generic solver chooses actual overlapping source parents, replaces one selected source component with actual source-core restrictions, recursively visits every raw output occurrence at `q-d`, and returns a checked minimum. Its disjoint case constructs literal ordinary restrictions, runs depth01, and executes the paid scheduler.

Run the author replay from the workspace root:

    ./bootloops-python research/rmaf/algorithm/universal233/forest_solver/replay.py

The replay rebuilds sources in a fresh result directory, audits all declarations by actual module origin and standard axioms, reruns controls, and catches deliberate source and audit corruptions. `LATEST-REPLAY.txt` identifies its receipt. A successful author replay does not constitute fresh nonauthor acceptance. All three main ordinary-tree algorithm, full runtime, and novelty milestones remain OPEN.

`SOURCE-WORK.md` states the immediate source-cost contract required by `source_work_bound`. The total bound is qualified by that contract; a polynomial coefficient and compiled-machine semantics are not proved here. `FIRST-GAP.md` identifies the remaining cost and external ordinary-tree obligations.
