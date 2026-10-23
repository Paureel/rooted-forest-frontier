# Consumer interfaces

| Consumer | Exact provided statement |
|---|---|
| Both-bad residual forest callback | `GenericForest.solve ordinary T ss q`, with literal optional target and literal current source trees |
| Correctness | `exact_of_ordinary ordinary ho : ExactAt (solve ordinary)`; only callback premise is the printed `OrdinaryIH` |
| Every returned forest | `solve_sound`; original finite state agreement and additional cost ≤q |
| Component replacement | `replacement_forward`, `replacement_reverse`, `emitted_replacement_cost`; original source embeddings come from actual `generate` |
| Overlap solution preservation | `overlap_child_covers`; actual selected index/output occurrence, original G preserved, exact d plus residual cost, residual ≤q-d |
| Child recursion | `branch_paid_proper`; actual raw occurrence has d≥1, d≤q and a proper replacement state |
| Query recursion | `actual_paid_query_smaller`; actual metered dispatch is a proper literal ordinary pair, budget≤q, smaller label count if at least two current sources exist |
| Raw recursive mass | `two_actual_cores_mass`; both full raw lists, rational c≥2, mass≤2/c |
| Work | `source_work_bound`; immediate nonrecursive contract `LocalBillBound` and nonnegative K, with total billed work≤(q+1)Kc^q |

The callbacks receive labelled forests, not recovered final source-cut lists. Final cut recovery remains the completed separate package. This generic solver does not construct the ordinary-tree dispatcher, a free whole-source-tree oracle, or an unconditional machine-runtime theorem.
