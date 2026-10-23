# Actual recovery source work

Lean derives structural unit-source work bounds for the actual initialization, helpers, recursive generator and final original-cut recovery. On checked P, the new recovery value equals `FinalCutRecovery.recover S P`, and its work is at most `64*(BudgetOptimization.recoveryEnvelope n+32)*2^(P.length-1)`, where n is the original source leaf count. The coefficient is polynomial in n. The `2^q` search factor remains; purely polynomial recovery time is not asserted. Scalar/bit/native interpretation, independent review and full 2.33/base/novelty acceptance remain open.

All public names have prefix `OrdinaryDispatch.RecoveryLocalWork`. Import RWInterface for the main result or RWRefusals for additional raw-refusal results. ACTIVE-v1.json names the canonical readonly receipt. The chosen import order is the new receipt, completed optimizer-fee package, completed own early package, completed budget package and the checker readonly dependency pool. IMPORT-COMPATIBILITY-v1.json records 425 shared source-identical module pairs and 16 differing compiled module pairs; the functional and binary-reference pools were not merged.

| Interface | Proved statement |
|---|---|
| `meterInitial_value`, `meterInitial_coloring`, `meterInitial_bound` | Exact initialization; coloring occurs once per original leaf only after nodup passes; actual non-color work fits frozen `128*(treeNodes t+1)^3` |
| `meterStep_value`, `meterStep_bound` | Exact step value; expanded helper work bounded by `localCap N+2*B+4*(R+1)` with explicit child work B and child receipt-record cap R |
| `localCap_eq_four_declared` | New `localCap N=1024*(N+1)^3=4*CoreWork.cap N`; no old localCharge primitive-dominance assumption |
| `meterRun_value`, `meterRun_bound`, `meterRun_closed` | Exact complete source receipts, including q=0 pruning; work bounded by `16*envelope q (localCap N)` under the purely structural Within condition |
| `meterGenerate_value`, `meterGenerate_bound` | Actual source generator value and work; arbitrary supplied color work is exposed as the sum over original leaves |
| `meterColor_value`, `meterColor_bound` | Literal block contains/early-stop/head scan; cost at most `32*(P.flatten.length+P.length+1)` per original label |
| `meterRecover_value`, `final_source_work_bound` | Exact final recovery; source bill at most `finalSourcePolynomial S P*2^(P.length-1)` |
| `final_source_uniform`, `final_source_absorbed` | Uniform polynomial coefficient `recoverySourceEnvelope n=64*(recoveryEnvelope n+32)`; absorption into any rational base c at least 2 |
| `optimizer_recovery_once_bound`, `optimizer_recovery_233` | The actual optimizer's single selected recovery has this new source bill; exact 233/100 absorption is proved |
| `final_source_refused`, `generate_source_refused` | Raw refused partitions have a literal node/block/cell guard bound; duplicate source labels refuse with zero coloring and no recursive run |

The checked recovery theorem assumes `(leaves S).Nodup`, `partitionCheck (leaves S) P=true`, and `pairwiseEmbeddings S P=true`. The actual optimizer theorem derives these from its selected agreement forest and proper original inputs. It retains every failed query trial in the frozen execution. No current-budget bound by a reduced state is used; generate accepts arbitrary budget and charges its actual min with the original leaf count.

The new polynomial coefficient is
`(guardCharge S P+colorCharge S P+initialCharge S+32)+32*(localCap (inputResource S)+6)*P.length`.
The source proofs derive helper costs first. Only then do they compare that coefficient with `64*(FinalCutRecovery.finalPolynomial S P+32)` and use the frozen polynomial arithmetic envelope. The proofs do not import the old local_le_cap, meterRun_bound, generate_work_bound or final_work_bound as primitive-dominance premises. Frozen constants and sources remain unchanged.

Groups and output appends pay their actual left-list lengths. Normalize pays repeated label appends. Address equality is expanded by its literal Bool-list comparator; erase and duplicate-cut tests include every visited comparison. Choose expands groups/all/find/filter/length/mixedCherry. Both attempted children, guard refusals, receipt counter updates, and budget-pruned calls are charged. The combined receipt pays both actual left receipt lists, even when their lengths are exponential in the budget. SOURCE-SHEET-v1.md gives the per-helper fees and premises.

The model counts structural reference/cell operations with explicit scalar unit slots. Nat equality/order, arithmetic, color labels, source counters and reference copies require a separate binary interpretation. Detached inner label lists, cut lists and returned objects are retained by reference where the source retains references; serialization is not performed by this source. Some meters conservatively charge suffixes that the source short-circuits. The result is a source upper evaluator, not a native compiler/runtime trace theorem.

Fifteen positive runtime checks passed, and twelve deliberately false propositions were rejected with `is false` diagnostics. Constructed two-child receipts at q=0,1,2 had summaries `(outputs,refusals,visited,attempts,pruned)` equal to `(0,0,1,2,2)`, `(0,0,3,4,2)`, `(2,0,5,4,0)`. An explicit coloring fee 11 produced coloring 11 and build work 19 on a singleton; duplicate labels produced zero coloring calls. Changed-hash, missing/duplicate producer and custom-axiom controls were rejected. The final audit retained full nonproof bodies and actual proof-reference/axiom walks for 326 stored occurrences across nine owned modules, with axiom union `Classical.choice`, `Quot.sound`, `propext`. All evidence has the same author/tool lineage.

For a fresh local replay, run verify.py first. Set RECOVERY_RECEIPT to a fresh relative directory and run run.py through `./bootloops-python` with `prepare`, then with `RWTree RWChoose RWLocal RWRun RWInitial RWFinal RWInterface RWControls RWRefusals`. Run `run.run('RWFalseControls',1)` with the same environment and then audit.py. No dependency is compiled. Each Lean process has a 60-second cap, 3072-MiB Lean memory limit, 3-GiB live disk floor and 16-MiB output limit; each producer record has an 8-MiB cap and compressed evidence a 256-MiB cap. Sealed sources/evidence remain immutable.
