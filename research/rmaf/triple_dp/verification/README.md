# Independent triple-DP finite verifier

This is a problem-specific fresh-author audit, deliberately separate from the production edge-cut oracle. `partition_oracle.py` enumerates set partitions, tests restricted rooted topologies by rooted triples, and computes minimal embeddings by unions of direct vertex paths.

Use it to replay the bounded ordinary rooted MAF completion campaign (no rho): incompatible source components must have exactly three leaves, while compatible components are unrestricted in the intended theorem. The completed corpus contains all 10,029 generated instances on n=1…5 fixed labels. This bound permits at most one bad triple, and compatible components have at most five leaves. The verifier does not prove the universal theorem.

Run from the workspace root. Keep the original receipts; choose unused output names for each replay. The sample replay names below are separate from the original frozen run:

```sh
./bootloops-python research/rmaf/triple_dp/verification/run_verification.py --mode controls --output research/rmaf/results/triple-dp-verification-replay-controls.json
./bootloops-python research/rmaf/triple_dp/verification/run_verification.py --mode pilot --output research/rmaf/results/triple-dp-verification-replay-pilot.json
./bootloops-python research/rmaf/triple_dp/verification/run_verification.py --mode full --output research/rmaf/results/triple-dp-verification-replay-full.json
```

A full-mode PASS means exact counts, cut conversion, returned-partition feasibility, and candidate characterization agreed on those 10,029 cases and 70,660 monochromatic partitions, for the solver hash recorded as `solver_sha256` in the full receipt. A FAIL throws and retains a failing input in the receipt. Universal correctness remains OPEN even on PASS. Frozen controls and hashes predate production access; the harness verifies six positives, five malformed inputs, five wrong results, and two mutant/clean-twin pairs before comparing the full corpus. Read WORK.md for provenance and the precise remaining graph lemmas. Reusing this corpus after adapting production to its findings is regression testing, not new held-out evidence.

The separate six-leaf supplement covers all 945 target trees and nine source-topology pairs on fixed sets abc and def: 8,505 cases and 212,625 partition checks. It includes 3,780 cases with two bad triples. The plan, hand controls, and pilot threshold were frozen in `supplement-n6-plan.json`; the original commands were `run_supplement_n6.py --mode pilot` followed by `--mode full`. Receipts are `research/rmaf/results/triple-dp-verification-n6-pilot.json` and `triple-dp-verification-n6-full.json`. That runner refuses to overwrite existing receipts. Both the original and supplemental results remain finite evidence; neither proves the unrestricted graph correspondence.

`referee_sim_PROOF.md` records a separate fresh review of the author’s proof, with exact post-hoc cut-accounting and normal-form examples in `triple-dp-verification-proof-scope.json`. These examples are separate from the independent comparison corpus. The 28 route theorem audits (19 core plus 9 semantic) and the fresh verifier’s 19 independently recompiled core audits have separate provenance.

The finite input domains overlap the route author’s earlier census. The independent reference code and its outputs were fresh; the inputs themselves were not previously untested by the author. Treat this as independent replication on a shared domain. The frozen supplemental script’s header uses “held-out” for reference outputs; that historical label does not establish input holdout.
