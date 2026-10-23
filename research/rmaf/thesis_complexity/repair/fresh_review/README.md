# Fresh G4 review programs

`RULING.md` states the result. `REVIEW.md` is the incremental read and execution record. All programs are one-shot review instruments; none is a replacement for the official toolkit or a theorem prover for rooted forests.

- `fresh_checker.py`: replays the five exposed controls with a new protected-tree implementation, exact fractions, simultaneous cut checking, source-priority cases and within-invocation reductions. Expected false assertions are retained and caught explicitly. Its JSON has one intentionally failed inner comparator record; the matching outer rejection record passes.
- `finite_attack.py`: enumerates local connected F2 trees against the fixed three/four-root F1 fringes. It checks the conditional C frontier estimate for K=0..7 and records exact failures. It imports only this review's fresh tree checker. No source-reachability claim follows from a zero-failure result.
- `interface_audit.py`: recomputes source use-site coefficients and offsets, the 37 multiplicative rows, exact A/B/C compositions and negative-budget boundaries. A failing abstract row does not constitute a source runtime counterexample.
- `additional_controls.py`: tests root-sibling exclusion, the arbitrary-double-cut failure with a positive twin, actual budget -4 on the thirteen-leaf history, and the invalid generic-A substitution.
- `mutation_audit.py`: weakens orientation on candidate copies and requires both the fresh geometry evaluator and Lean to reject the false claim. Original candidate files remain untouched.
- `lean_review.py`: compiles verbatim candidate copies with extra axiom queries for every theorem; checks import/declaration restrictions and records source hashes.

Use `./bootloops-python` from the workspace root for each Python file. The Lean audit calls `./bootloops-lean`. A failed assertion is a failed review check unless the explicit negative-control wrapper expects that exact failure. All exact comparisons use integers or Fraction; there is no numeric tolerance.

Calibration preceded candidate reading. The finite conditional test followed candidate reading and was targeted at the candidate's stated hypotheses, so it is described as fresh implementation evidence, not a held-out experiment. The required wrong-orientation and reverse-twin controls demonstrate that the minimum-cut assertion can both fail and pass. The source and control files are shared inputs; no author-side checker code is imported.
