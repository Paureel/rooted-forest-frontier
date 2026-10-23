# Consuming theorem trace

| Input or producer | Actual consumer | Discharged condition |
|---|---|---|
| literal `allGood T ss = true` | `allGood_parts` | proper source-label partition and full-source restricted topology |
| literal proper check | `owner_lt`, `actual_paint_spec` | owner indices are available finite colors; nonempty ordinary target has a nonempty color list |
| `table_spec` | `solve_spec` | actual finite table soundness and minimum among all admissible colorings |
| `solve_spec` and proper | `candidate_partition`, `candidate_ownership` | exact original labels, unique coverage, nonempty blocks, actual source containment |
| actual `split` components | `split_certificate`, `candidate_embeddings` | original unsuppressed target minimal spans are pairwise disjoint |
| full-source target restriction isomorphism | `full_source_iso`, `iso_restrict`, `iso_clear` | actual source restricted topology and span/minimal-disjointness transport |
| original partition, containment and target embeddings | `allGood_completion`, `candidate_agrees` | every original `ForestState.agrees` conjunct, with no graph facts supplied as fields |
| arbitrary competing literal `agrees` | `recover_checked` on the target | actual original cut count |F|-1 and realized components, retrieved from the completed frozen package |
| those actual realized components | `realized_coloring`, `agreement_coloring` | admissible owner coloring with at most |F|-1 changes |
| all-coloring DP minimum and converse coloring | `candidate_blocks_minimum`, `candidate_minimum` | minimum among all literal checked ForestState agreements |
| source-label partition and refinement | `sources_le_blocks`, `additional_exact` | |F| is at least |ss|; natural subtraction equals the exact source-count difference |
| actual minimum | `decideBudget_correct`, `run_total_exact` | exact result and correct existential decision for every natural budget |

`ConsumerControls.literal_case_for_every_budget` applies the interface without
extra clearance, group isolation, special labels, search bounds, or desired
output fields. `DPControls` executes the actual candidate on the pinned
examples; `ConsumerControls` executes the two positive-budget thresholds and
the none boundary. `COST-MODEL.md` identifies the executable call graph and
the separate logical converse dependency.
