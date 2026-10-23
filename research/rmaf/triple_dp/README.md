# Triple-component completion instrument

This problem-specific instrument implements the proposed exact rooted-tree/source-forest completion DP when every incompatible source component is a triple. Its full graph theorem remains open. Input leaves are unique nonempty strings; internal vertices are two-element arrays; the source is a list of nonempty component trees. Every target label must occur once in the source. There is no implicit rho leaf or acyclicity requirement.

Use this at an already-reached source-forest state. For an unrestricted instance outside the class, the solver raises `ValueError`; arbitrary pre-cutting is not a safe entry procedure. The neighboring `../oracle/` instrument handles unrestricted small-instance discovery. This route deliberately has a separate implementation lineage.

`solver.py input.json` returns `components`, `additional_cuts`, `partition`, `bad_components`, and exact core operation counters. Components means final forest blocks; additional cuts subtracts the number of source components. A returned partition must pass a separate graph witness checker. The current mathematical result is a proposed exact terminal theorem with explicit formal gaps, documented in `PROOF.md`.

Replay from the workspace root:

```sh
./bootloops-python research/rmaf/triple_dp/check.py controls
./bootloops-python research/rmaf/triple_dp/check.py census --n 5
./bootloops-python research/rmaf/triple_dp/check.py census --n 6 --two-triples
./bootloops-python research/rmaf/triple_dp/audit_lean.py
./bootloops-python research/rmaf/triple_dp/audit_connected.py
./bootloops-python research/rmaf/triple_dp/large_checks.py
./bootloops-python research/rmaf/triple_dp/mixed_checks.py
./bootloops-python research/rmaf/triple_dp/reachable_child.py
```

The census compares against independently written graph edge-cut enumeration by the same author, which is exponential and restricted to small trees. It checks all accepted partitions as well as optimum and witness. `large_checks.py` performs witness-only scale checks and a source-verified baseline child example; its large values are not independently certified optima. The frozen five positive, five malformed, and three destructive/claim controls must pass or be caught. `mixed_checks.py` tests the frozen post-hoc compatible-four-leaf/bad-triple sample. `reachable_child.py` certifies a legal nine-leaf baseline child with two overlapping bad triples and a matching three-cut obstruction and witness. Fresh-author verification lives in `verification/`; its n≤5 and fixed-two-triple n=6 checks passed, and the full graph theorem remains open.

The core costs O(nm) values/backpointers and O(n) reconstruction on the stated word-RAM model, with polynomial validation outside that bound. The Python research implementation uses recursion and may hit the interpreter recursion limit for very deep input trees. `TripleDP.lean` checks a general min-plus tree-automaton theorem and supporting lemmas; it does not assert the missing graph correspondence. `SemanticControls.lean` shares the existing RMAF executable model. `ConnectedRegions.lean` proves a single-region root/child path-convexity decomposition; the family/cost correspondence is still open. `NegativeControl.lean` and `NegativeConnected.lean` must fail and are never imported as theorem libraries.

2026-10-14: created and tested this independent research route after consulting BootLoops and the nearest oracle guide. No upstream scripts or pins changed. The original census oracle bytes are retained as `cut_oracle-census-v1.py`; the live oracle adds a witness-only graph checker. This project-specific capability is indexed by this README and the route's dashboard artifact list rather than added to the unrelated general BootLoops toolkit.
