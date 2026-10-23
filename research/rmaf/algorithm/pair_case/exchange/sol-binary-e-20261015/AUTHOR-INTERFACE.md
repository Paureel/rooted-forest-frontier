# TARGET-v1 E to Lean map

Author map only. This is not the required fresh nonauthor consumer ruling. Main profile/scaffold consumer sources were deliberately not read by this arm.

| TARGET E object or condition | Actual formal representation | Source |
|---|---|---|
| Original binary distinct-label S,T, equal labels | `RMAF.Tree`, `(leaves s).Nodup`, `(leaves t).Nodup`, explicit membership equivalence | Exchange.lean:88 |
| Proper P with disjoint actual source embeddings | `partitionCheck (leaves s) P=true`, `pairwiseEmbeddings s P=true` | Exchange.lean:88 |
| Distinct parents A,B | `A∈P`, `B∈P`, `A≠B` | Exchange.lean:88 |
| Oriented original target edge, descendant D | nonempty `v`, `treeAt t v=some u`, `D=leaves u` | Descendant.lean:5; Exchange.lean:88 |
| Four nonempty sectors | `mixed A D.contains=true`, `mixed B D.contains=true`; `mixed_iff` gives both sector witnesses | Surgery.lean:118 |
| Actual bilateral mutual clearance | four `Disj` hypotheses; equivalent to original `disjointVertices minimalVertices` | Exchange.lean:88; imported Bridge.lean |
| Other parent clearance | every E∈P distinct from A,B has `Disj t E A ∧ Disj t E B` | Exchange.lean:88 |
| A's rooted restrictions agree | `restrictionAgrees s t A=true`; `sameShape_correct` links Boolean and RootedIso | Exchange.lean:88; original RMAF.lean |
| Every actual F refining P | arbitrary `F`, `agreement s t F=true`, explicit `Refines F P` | Exchange.lean:88 |
| Construct actual F' | executable `exchange`, assembled from label filters | Exchange.lean:82 |
| Whole A, one copy | `F'.count A=1` | Exchange.lean:64,88 |
| B blocks on one D side | quantified label-membership dichotomy for every C⊆B in F' | Exchange.lean:88 |
| Outside blocks unchanged | equality of outside-filter lists, preserving their order | Exchange.lean:19,88 |
| Nonincreasing component count | `F'.length≤F.length`, proved by original-vertex ownership | Count.lean:26; Exchange.lean:88 |
| Actual agreement bridge | all five Boolean constituents, not an abstract forest-validity predicate | Surgery.lean:39 |
| Proper source edge for split | nonempty source address w, actual treeAt, color equivalence restricted to agreed final C | SourceEdge.lean:54 |
| Residual source operations and charged cost | OPEN; not a premise or conclusion of E | REPORT.md literal source witness section |

The exported theorem retains some unused premises from the printed target: source distinct labels/equal labels, nonroot v, B mixed, the A-sector half of mutual clearance, and other-parent clearance from B. The proved surgery needs the remaining premises and does not silently strengthen any target hypothesis. Empty, absent, or repeated-label cases outside the printed hypotheses are not admitted by an unqualified application.
