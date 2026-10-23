# Source cost contract

`sourceWork` counts natural source-operation bills embedded in exact rationals. Its recursive cases follow the same guards, current target/source lists, actual overlap indices, literal raw occurrences, and checked subtraction as `solve`. A completed state contributes only its local bill; a singleton adds its ordinary callback bill; a disjoint state adds `PaidQueries.meterSchedule` caller and exact ordinary-query work. An overlapping state adds both generation bills, every replacement/materialization bill, minimum-selection bills, and all recursive forest calls.

The source-operation convention charges list/constructor operations and scalar Nat operations. The coefficient must absorb scalar encoding costs when those operations are implemented on unbounded integers. Computing the accounting functions themselves is excluded. The claim concerns source inspection and does not identify compiler instructions.

| Bill | Definition and retained evidence |
|---|---|
| Guard/check/depth01/restriction/selection inspection | `inspectionBill = 4096*(targetNodes+sourceNodes+sourceCount+q+1)^8`; declared conservative local contract, still requires primitive source review |
| Actual vertex search | `overlapBill` includes all ordered current-source pairs, both literal target minimal spans through completed `meterMinimal`, and full address-membership upper charges; rejected i<j pairs are overcharged |
| Generation prefixes, failed attempts and pruned continuations | Completed `CoreWork.meterGenerate`; its receipt projection and work envelope are retained from the completed source-work package |
| Original-target region coloring | Sum of `WholeSourceWork.meterColorLabel t v x` for every original leaf of the selected current source; no unit-cost color oracle |
| Source replacement and output materialization | `materializationBill` on every raw occurrence includes literal replacement-tree inspection, original state inspection, partition label cells and original cut-address cells |
| Actual ordinary calls | `PaidQueries.meterSchedule_trace` bills exact dispatched problems and budgets, including failure; `actual_paid_query_smaller` proves properness, budget ≤q, and strict label decrease with multiple sources |
| Returned minimum | The inspection charge is repeated for every raw occurrence plus the outer minimum; failed/pruned occurrences are overcharged and duplicates are retained |

`proper_source_size` proves `sourceNodes ss + ss.length = 2*|labels T|` for every proper state. Every emitted replacement is proved proper at the consuming recursive call. No new labels or unbounded source-tree volume can accumulate in the forest recursion.

For fixed initial target T and budget cap Q, `LocalBillBound` assumes the printed immediate bill is at most `K*c^b` for every proper current source list and every `b ≤ Q`. This assumption includes the supplied ordinary-work bills and excludes all generic forest recursive work. Under this contract, `source_work_bound` proves

    sourceWork ordinary ordinaryWork T ss q ≤ (q+1)*K*c^q,

for exact rational `c ≥ 2`, `K ≥ 0`, `q ≤ Q`, and a proper state. Each actual child has cost `d ≥ 1`, so its linear factor is at most q. The two actual raw source-core lists have mass at most `2/c ≤ 1`; no duplicate is removed. The local bill supplies the remaining one unit in the linear factor. A polynomial K and the source-check-to-bill correspondence remain the cost review obligation in `FIRST-GAP.md`.
