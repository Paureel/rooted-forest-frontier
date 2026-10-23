# Final original-source cut recovery

`RecoveryProgram.lean` returns the actual original cut certificate for a checked source partition, after a minimum labelled agreement has been chosen. The source generator is unchanged. `Recovery.lean` proves exact original realization and cost, and agreement preservation under actual block/label permutations. `FinalWork.lean` composes a complete all-prefix work envelope with finite input checks and color scans. Fresh nonauthor acceptance is pending; all three complete-algorithm milestones remain OPEN.

The replay command is:

    ./bootloops-python research/rmaf/algorithm/universal233/final_cut_recovery/replay.py

The script copies and rebuilds all exact completed rank/cut/source/core-work dependencies in a new results directory, with only that directory on LEAN_PATH. It audits every declaration by actual module origin, including private/generated declarations. It requires only standard axioms, catches missing audit rows and a hidden custom axiom, rejects false propositions, and catches source-pin corruption. `run_controls.py` is the preserved pre-proof finite control runner.

Read `INTERFACE.md` for hypotheses, `COST-MODEL.md` for the source-operation qualification, and `FIRST-GAP.md` for remaining work. Frozen manifests and receipts must be preserved; later repairs require a new version.

After `FINAL-CUTS-MANIFEST-v1.json` exists, replay.py leaves all owned files untouched and creates only new results evidence. Preserve the frozen LATEST-REPLAY pointer as the author certificate of record.
