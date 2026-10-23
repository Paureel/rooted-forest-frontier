# G consumer trace

| Consumer requirement | Supplied theorem / executable | Exact premise and scope |
|---|---|---|
| Original full target tree | RMAF.Tree and original `vertices`, `edges` | Actual binary input; no root stem and no suppressed edge interpretation. |
| Distinct proper labels | `properInput`, `proper_nodup`, `proper_disjoint`; `choose_sound` | Concrete finite checks also reject absent/repeated/empty selection labels. |
| Actual hull interpretation | Frozen `Bridge.minimalVertices_correct`, source-hashed replay | Original unsuppressed minimalVertices equals selected original leaf-address Hull, including empty and singleton cases. |
| Nonlabel shared vertex | Frozen `disjoint_parent_overlap_nonlabel` | Actual disjoint original A/B labels; derived from actual executable overlap. |
| Occupied region ↔ adjacent hull vertex | `realized_neighbor`, `hullNeighbors_actual` | Occupied nonlabel vertex; neighbor is original parent/child direction and actual edge. |
| Degree is the actual distinct count | `neighbors_nodup`, `hullNeighbors_nodup`, `region_count_actual_hull_degree` | Count equals the length of all distinct actual adjacent embedding vertices. Root has no upward neighbor. |
| Shared original edge | `shared_edge`, `minimal_vertices`, `child_actual_edge` | Derived from actual nonempty overlap and binary address directions. Neither a shared-edge field nor degree-two-path conclusion is assumed. |
| Failure of sector clearance | `three_of_sector_collision` | Actual sector leaf addresses, opposite nonempty sector and actual other-parent hull; produces a shared3-region point by four-set Helly. |
| Complete geometric alternative | `actual_selector_exists` | Proper distinct original leaf labels, disjoint A/B, actual nonempty overlap. Conclusion contains an actual edges-list member, all4 nonempty label sectors and both full mutual-clear predicates. |
| Original descendant D | `descendants_mem`, `leafAddress_correct`, `selected_side`, `sector_hull_correct` | Unique original leaf address from Nodup original labels; sideLists are exactly A/B intersect D and complement. |
| Executable selection | `choose`, `choose_sound`, `choose_complete` | Total finite original-vertex/edge scan. No source optimum oracle. |
| Narrow two-region consumer | `choose_binary_when_two` | Both region counts2 at every actual shared vertex; returned choice must be an actual edge. |
| Outside disjoint/singleton regime | `choose_none_without_overlap`, literal controls | No overlap yields no accepted choice, not a new G instance. |
| Candidate scan overhead | `chooseCalls_linear` | At most4n−3 predicate calls. Per-predicate tree/list work is polynomial by source structure; full solver runtime is not claimed. |
| Correct reached-state inputs | Not supplied by G | The caller must provide the original target and correct expanded original A/B labels. State history stays OPEN globally. |
| E, source core, original source cuts and full recurrence | Not supplied by G | Separate targets. G supplies only target geometry and selection. |

The accepted theorem chain has no assumed selector or mutual-clear conclusion. A nonauthor consumer review must still rule that the algorithm calls it with its exact original-label/history premises. The source-bound author receipt and finite controls do not replace that review.
