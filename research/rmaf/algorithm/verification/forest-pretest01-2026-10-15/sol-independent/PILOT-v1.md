# Measured prerelease pilots

Graph pilot v1 completed PASS on singleton and crossed current forest in
0.001418875 seconds total (Python 3.12.14; same graph/partition code and
settings as planned full controls). Evidence: graph-pilot-v1.json, which pins
the script and fixture hashes. Free space after pilot: 4,222,636,032 bytes.
Startup dominates this small measurement, so no steady-state rate is claimed.
The full controls have only 13 base fixtures and 14 symmetry/label variants,
with Bell(5)=52 set partitions at the largest fixture; expansion remains
bounded by the same 30-second alarm, rather than an unsupported long-run ETA.
Scientific progress unit: completed exact fixture/control records. Proceed
with the hand-fixture battery only. No census or blanket suite is licensed.

Producer detector pilot: pending runtime path from root. No candidate read.

Graph full hand battery v1: PASS, 27 fixture records and 14 corruption catches,
0.015783334 seconds, free space 4,217,094,144 bytes. Exact fixed controls
all reproduced, including five crossed-current-forest candidates with four
accepted entries but two distinct partitions; seven crossed-single-source
candidates with none accepted. No evaluator repair or failed run occurred.
The hidden-source validator-only fixture also measured minimum two; that
extra numerical observation was not a preregistered expectation and remains
an exploratory finite observation. Evidence: graph-controls-v1.json.

Producer recorder compile v2 PASS in 0.871994042 seconds (v1 failure retained).
Synthetic clean-module pilot v1 PASS: two commands completed in 0.963273958
seconds total, three stored raw producers, all three bodies available, no
axiom false alarm. Same runtime/recorder/settings will run the full synthetic
module battery. At two pilot commands per 0.9633 seconds, a flat eight-command
projection is about 3.85 seconds; compilation/startup and collision processing
may change that rate, so this is a bounded planning estimate rather than a
steady-state fit. Keep the 60-second per-command cap and record actual times;
no long job is launched. Free space after pilot: 4,114,382,848 bytes.

Producer full hand controls v3 PASS: 19 controls, 11 measured commands,
4.886472125 seconds total, free space 4,099,710,976 bytes. The original
construction failures remain in their receipts and failure ledger. Both
conflicting import orders are refused by Lean before recorder execution;
separate environments retain the two same-name, same-type values 7 and 11.
All actual stored types, bodies and opaque values in the controls were
recorded as explicit expression DAGs. Name/binder annotations were preserved;
Syntax-valued expression metadata is a deliberate fail-closed scope limit.
