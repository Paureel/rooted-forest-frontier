# Degree-two proof checkpoint

Use `lean/ActualRefinement.lean` for an actual two-piece refinement and its original agreement-partition consumer. Input hypotheses and remaining global scope are listed in `REPORT.md`; the immutable target is `../DEGREE-TWO-TARGET.md`.

The source-bound author replay is:

```sh
./bootloops-python research/rmaf/bridge_review/degree_two/replay_final.py
```

It creates a fresh local build directory, verifies completed dependency hashes, rebuilds every production and control module, inventories named declarations and their printed axioms, and requires explicit falsity from planted wrong proofs. A malformed proof of True is separately required to fail, while its clean twin compiles. All old proofs remain untouched. `FINAL-REPLAY.json` points to the most recent successful receipt; unsuccessful attempts cannot replace it.

This script audits source and kernel evidence. It does not independently validate the graph semantics or promote finite tests into a theorem. The separate nonauthor checker and interface trace in `fresh_review/` supply that review. Each route has its own immutable control/route pin and retained failed attempts. All imports are the unchanged RMAF and completed bridge sources, Lean's standard library, and this new increment.

`audit_one_tree.py` is the earlier scoped author checkpoint; its status and transport boundary are historical. `graph_route/` and `restriction_route/` preserve independently derived routes. These are problem-specific proof/audit instruments, so no general toolkit package was added. No upstream verification source, integrity pin, frozen result, hosting service or deployment was changed.

2026-10-14: first implementation; no previous caller or output format was replaced. Full toolkit, new larger searches, runtime and novelty audits were not run because this increment claims only the pinned proof interface.
