# Fresh graph semantic review

The graph-model semantic check is confirmed: a finite nonempty support connected by one-bit parent/child edges has a unique minimum-depth root, and retaining that support at this root realizes the existing `PureBridge.RootedRegion`. The independent finite enumeration and direct proof inspection agree on that meaning. The universal statement comes from Lean's proof; the enumeration checks a finite interpretation independently.

I found one defective negative test. The initial `FalseSuppressParent.lean` used `decide` without unfolding `Adj` and failed because no `Decidable` instance was synthesized. A true-edge twin failed identically. Unfolding `Adj` made the true edge compile and the false two-bit edge fail with a falsity diagnostic. The theorem proof itself was unaffected. The author corrected the control, added a passing true-edge twin, required explicit falsity diagnostics in the audit, and preserved the earlier files. Fresh replay of the corrected sources passed; source hashes and axiom reports match the rebuilt certificate (`lean_receipt.json`).

## Independent evidence

I read `research/rmaf/spec.json` first and wrote this review's skeleton immediately. `CONTROLS.json` was frozen before GraphRegion, GraphControls, the original consumer, the certificate, REPORT, or any existing review Python was read. SHA256: `6cf15c63401c52dbc6ac211b3851456bb94da3517ca4421d10a2f45a36e0f269`. Integer heap vertices, raw adjacency closure, and integer parent division supplied a separate representation and implementation. No campaign or review Python source was read or imported.

The eight hand controls include a singleton away from the ambient root, a retained degree-two chain, a fork below the root, a complete height-two tree, disconnected equal-depth vertices, a missing intermediate vertex despite a unique minimum, a nonminimum root in a connected support, and the empty set. Every expectation matched. Three deliberately incorrect comparator expectations were rejected.

| Enumeration | Exact count |
|---|---:|
| All height-three subsets, including empty | 32,768 |
| Nonempty connected supports | 750 |
| Nonempty disconnected supports | 32,017 |
| Support/root pairs tested | 245,760 |
| Wrong-root rejections within connected supports | 5,636 |
| Semantic mismatches | 0 |

The executed receipts are `pilot.json` and `enumeration.json`. They record the script and control hashes, denominators, and elapsed time. All semantic arithmetic is exact. Finite sets remain finite evidence, regardless of their number.

## Source reasoning

`GraphRegion.lean:9–14` uses one-bit adjacency and finite walks constrained to the support. `ConnectedSupport` at lines 87–91 contains a first vertex, a finite remaining list, and pairwise walks; it assumes neither ancestry nor convexity. `exists_shortest` derives minimum depth from the list. `walk_below_minimum` derives ancestry, and `walk_ancestor_between` derives retention of every intermediate ancestor. Lines 106–112 therefore supply all three proof fields of `PureBridge.RootedRegion` (original consumer lines 14–19) without assuming them. Duplicates in the support list do not affect membership.

`root_unique` at lines 116–120 proves uniqueness from the two minimum-depth inequalities and prefix ancestry. The constructor uses `Classical.choose`; it is noncomputable. `deepest_graph_root_in_neighbor` at lines 123–127 invokes the original `PureBridge.deepest_root_in_neighbor` directly, with the original depth and overlap hypotheses and the unchanged membership predicate. Reusing that same root proves all pairwise neighbor intersections. This composition concerns the original consumer, not a simplified replacement.

The wrapper `MinimalEmbedding` at lines 145–155 assumes a connected support, ambient inclusion, terminal inclusion, and leastness among such supports. It supplies no label map, leaf condition, distinct-terminal proof, or well-formed ambient tree. The initial comment overstated distinct terminals. The corrected comment and REPORT line 9 now explicitly name these absent invariants. The graph theorem does not use them, and its proof bodies are unchanged.

The original `ExchangeSystem.freeLeft`, `freeRight`, and `clearRest` are assumptions at PureBridge lines 75, 76, and 79. The new graph construction does not instantiate them for agreement forests. `free_replacement` and `free_minimum` use `freeLeft`; `paid_replacement` uses `clearRest` and `freeRight`. Those universal exchange obligations remain open.

## Acceptance scope

Only the new graph-model semantic check is confirmed. The executed Lean builds reproduce the same kernel and original dependency, while the independent Python enumeration supplies finite semantic controls. The full G1 executable encoding/extraction link, universal G2–G7, unrestricted safe coverage, recurrence and termination analysis, the requested faster bound, and novelty remain unresolved. This review neither inspected the earlier geometry oracle nor audited external prior art.

`referee_sim_REPORT.md` records separate correctness and novelty objections for formal-method, rMAF, numerical-check, practitioner, and general-reader audiences. The corrected report snapshot, original certificate, and failed-control diagnostics are retained. The corrected report was read again, including its opening paragraph; no unresolved finding remains within this graph-model scope.
