# Optimizer wrapper work

Lean proves the actual optimizer wrapper's value correspondence and concrete structural operation fees: preflight `256*(N+1)^2`, each visited trial `12`, and final administration `32`. The final recovery wrapper has an exact value proof and a raw guard bound, but the old recovery generator's source interpretation remains open. Solve callback costs, scalar bit costs, native execution, independent review, and full algorithm/base/novelty acceptance are also open.

All public names have prefix `OrdinaryDispatch.OptimizerLocalWork`. Import OWOptimize from the canonical receipt in ACTIVE-v1.json, with the exact completed early, budget and transitive dependency modules recorded by FINAL-MANIFEST-v1.json. For original input trees T,S assume only `treeNodes T≤N` and `treeNodes S≤N`. The scan and guard results also cover malformed input, failed callbacks and raw payloads that will be rejected.

| Public result | Meaning |
|---|---|
| `meterPreflight_value`, `meterPreflight_bound` | Properness and literal leaf-list/count work; bound `256*(N+1)^2` |
| `meterScan_value`, `meterScan_accounting` | Exact frozen scan value; work equals all retained callback charges plus administration |
| `meterScan_administration` | Administration at most `12*trials.length+2`; at most fuel trials, with no payload traversal |
| `meterFinish_value`, `meterFinish_bound` | Exact frozen final record, one selected recovery only; at most 12 additional structural slots |
| `meterOptimize_value`, `actual_wrapper_fees` | Exact optimizer value, with `meterOptimize.work≤totalCharge w (preflightFee N) 12 32 S (optimize T S)` |
| `wrapper_polynomial` | The sum of all three wrapper fees is at most `512*(N+1)^2` |
| `actual_trial_budget_cap` (OWBudgets) | Every actual trial budget, including failures, is below the original input leaf count |
| `meterInputCheck_value`, `meterInputCheck_bound` | Exact recovery input guard; at most `2048*(R+1)^5` for raw node/block/cell caps R, without acceptance |
| `recovery_guard_covered` | The derived guard plus literal P.length/head/control slots fits within the old guard coefficient |
| `meterRecovery_value`, `meterRecovery_le_legacy` | Exact final recovery value; new counter does not exceed the legacy meterRecover counter |
| `conditional_233_derived_wrapper` | The frozen conditional 233/100 counter theorem with the three fees instantiated and actual solve callback work w still explicit |

`meterOptimize w` executes the frozen solve value at each visited budget and assigns that callback the explicit charge `w b`. The definition supplies no proof that w covers solve. Its runtime arguments contain no supplied whole-wrapper LocalCost or desired preflight/trial/final fee. Forests, returned certificates and retained trial entries are references in this structural model. Traversing or serializing those payloads requires additional operations if a consumer performs it.

The actual call starts at zero with fuel equal to the original T leaf count. All failed trials before the first success remain in order. The scan may also exhaust its fuel; no recovery occurs then. Its generic local theorems permit arbitrary starts and callback payloads. Preflight conservatively charges the leaf count even on malformed refusal, and the final fee also covers the scan terminal branch and outer record construction. Nat equality/order, successor, arithmetic and label copies remain explicit scalar unit slots, with their binary interpretation external.

The new recovery guard expands both leaf materializations, nodup, partition checks and pairwise hull tests. It uses literal raw node/block/flattened-cell sizes. Coloring uses the already completed literal blockColor/meterColor scan, evaluated once per original leaf during generator initialization; each color charge is bounded by the actual block/cell sizes. P.length traversal, subtraction, final head? and record slots are explicit. The generator call is the unchanged `CoreWork.meterGenerate`; FIRST-GAP-v1.md identifies the precise unsupported source interpretation of its assigned initial/local charges. The exact value theorem does not settle that cost statement.

Positive controls checked the zero-fuel baseline, failed-then-successful scan (callback sum 3, administration 24, total 27), three failures (administration 38, total 41), original singleton/identical/triple optimizer summaries, malformed refusals, exactly one final recovery, and raw recovery guard rejection. Guard work was 87 for singleton [[7]] and 34641 for forty repeated raw blocks. All ten runtime checks returned true. Ten false propositions were rejected, and changed-hash, missing/duplicate producer and custom-axiom controls were caught. The producer audit retained full nonproof bodies and actual proof-reference/axiom walks for 124 stored occurrences across five owned modules; its axiom union is `Classical.choice`, `Quot.sound`, `propext`. These checks share the author and tool lineage.

To replay locally, first verify FINAL-MANIFEST-v1.json using verify.py. Set OPTIMIZER_RECEIPT to a fresh relative result directory, then run this directory's run.py via `./bootloops-python` with `prepare` and with `OWScan OWRecovery OWOptimize OWControls OWBudgets`. Execute `run.run('OWFalseControls',1)` with that same environment, then audit.py. No dependency is rebuilt. Each Lean process has a 60-second cap, 3072-MiB Lean memory limit, 3-GiB live disk floor and 16-MiB output limit. Use a new result directory; sealed sources and evidence remain immutable.
