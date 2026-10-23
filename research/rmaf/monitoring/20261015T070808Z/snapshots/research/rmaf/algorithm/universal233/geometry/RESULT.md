# Vertex geometry: Lean proofs, algorithm still conditional

Lean checked the original-address graph claims needed by the vertex ownership proposal. The source-core generator, its original-edge witnesses, its work bound, and the state-machine history invariants remain separate obligations. These files establish no 2.33 algorithm or novelty claim. A fresh nonauthor proof and interface review is still required by prove-protocol.

Replay with `./bootloops-python research/rmaf/algorithm/universal233/geometry/audit.py` from the workspace root. The retained `audit-run.log` reports positive builds, complete axiom lists for 129 theorems, and rejection of both false propositions. `certificate.json` records source hashes and individual build times; `axioms.log` retains every printed axiom list. The only allowed axioms are Lean's standard `propext`, `Quot.sound`, and `Classical.choice`. The count includes the imported original `research/rmaf/lean/RMAF.lean`; it does not count 129 independent mathematical results.

## Graph model

A vertex is its original `List Bool` address. `PathAt v a b` describes the unique path between addresses `a,b` in the binary parent/child graph, retaining its endpoints. `Hull S v` means some path between two selected leaf addresses contains `v`; a singleton leaf has its own one-vertex hull. `region v a` identifies the upward or one of the two downward components after deleting `v`. The special value 3 denotes the deleted vertex and is excluded for labels at an overlap.

The executable identification is `Bridge.lean:270`, `minimalVertices_correct`:

```
v ∈ RMAF.minimalVertices D t ↔ Hull (selectedLeaves D t) v.
```

The theorem holds for every binary `RMAF.Tree`, every selection, and every address. It includes empty selections and singleton selections. It is proved from the recursive executable definitions of both `rootedSpan` and `minimalVertices`; it assumes no hull equivalence or core property. `hull_convex` then proves path convexity of these actual minimal embeddings.

## Consumer results

| Proposal call | Proved statement and exact assumptions | Lean location |
|---|---|---|
| Clique selector, integration lines 15–16 | Three pairwise-intersecting executable minimal spans have a common vertex. `findCommon` returns one and checks at most the number of vertices in the first span. No shared edge is assumed. | `Bridge.lean:362`, `:686` |
| Nonterminal overlap, lines 18–19 | Disjoint original parent labels imply an overlap vertex is not a selected label of either parent. An occupied nonlabel span has exactly 2 or 3 nonempty leaf regions. | `Bridge.lean:348`, `:427` |
| Region coloring, lines 16–18 | A piece avoids a nonlabel vertex iff its leaf addresses all have the same deletion region. Under distinct proper input labels, the same equivalence holds for the concrete original-label function `colorLabel`. | `Bridge.lean:371`, `:588` |
| Double-removal coloring, lines 26–28 | Equality of the pair of deletion directions is equivalent to the unique path avoiding both removed vertices. This is the exact component relation, including leafless middle components. | `Geometry.lean:613` |
| Chain target selection, line 25 | Disjoint endpoint embeddings force selected overlap vertices to be distinct. | `Bridge.lean:626` |
| Joint region branch, lines 31 and 35–42 | If B occupies a nonlabel `v`, its double-removal leaf-color list has at least two elements. Hence the executable branch is count 2 or count at least 3. | `Bridge.lean:478`, `:513` |
| Coincident occupancy, lines 35–40 | If B occupies both nonlabel targets and exactly two joint leaf colors occur, every subset P of B occupies v iff it occupies w. | `Bridge.lean:389`, `:488` |
| Clique ownership, lines 15–22 | A valid original `RMAF.agreement` partition, grouped into distinct source parents with disjoint original labels, satisfies one of the three two-parent clear alternatives. | `Composition.lean:134`, `:158` |
| Chain ownership, lines 24–33 | The same actual agreement and label-group hypotheses imply the four stated clear assignments. | `Composition.lean:170` |
| Paid coincident case, lines 35–40 | Under the actual B-subset and count-2 hypotheses, the valid final partition clears B at both targets, or clears A at v and C at w. | `Composition.lean:185` |
| Refinement composition | If the final partition refines an emitted core partition and that core partition avoids a target, the final partition avoids it. Refinement is transitive. | `Composition.lean:13`, `:29` |

For a single deletion, `sameRegion_iff_path_avoids` proves component membership directly. For a double deletion, `jointRegion_iff_path_avoids` applies the single-deletion theorem twice. Paths between parent labels remain in the parent hull by `hull_convex`; therefore the component signatures describe deletion from the parent embedding itself, not connectivity through vertices outside that parent.

The clique proof uses the median of three pairwise intersection witnesses. The median lies on each of their three connecting paths, so path convexity places it in all three parent embeddings. The concrete selector scans the first executable span and checks list membership in the other two. Every list consists of original addresses in a finite input tree; constructing these lists and scanning them takes polynomial work. Only the exact predicate-call bound has a Lean cost theorem here; the full solver's cost remains unproved.

For the count-2 chain, choose the two nonempty joint leaf components. Occupancy of v forces their v-coordinates to differ. Occupancy of w forces their w-coordinates to differ. Each coordinate therefore induces the same two-class partition of B's leaves. Every subset P has a monochromatic v-coordinate iff it has a monochromatic w-coordinate, and the avoiding-region theorem gives coincident occupancy. This argument does not sum two same-parent cut sets.

## Boundary conventions

The original input root has no upward leaf region. `executable_root_region_count_two` proves exactly two regions whenever the input root is an occupied nonlabel target. No rho leaf or artificial stem is present. A singleton selected label occupies its own leaf, so the nonlabel hypothesis is essential and is retained at every avoiding-region use.

Leafless components contribute no color: `regions` filters realized directions, and `jointColors` deduplicates pairs realized by selected original leaves. The root of the retained chain control is a leafless middle component after deleting the two targets. The full parent B has two joint leaf regions in that control.

Unary suppression is confined to rooted shape restriction. Collision checks and selectors use the fixed full original target tree and original leaf-label sets. `minimalVertices_correct` proves that all unary path addresses retained by `rootedSpan` have the intended collision meaning. The proposal can recompute target embeddings from original labels after every source operation; it need not compare addresses from suppressed restriction trees. Proving that every reachable source state carries the correct original-label sets is still part of the source-state invariant below.

Proper original labels matter for coloring a taxon once. `original_label_avoids_iff` requires `(RMAF.leaves t).Nodup` and that every selected label occurs in `t`. It proves uniqueness of the selected leaf address and uses the concrete `colorLabel` at that address. The ordinary `RMAF.Instance` supplies identical bijective taxon sets; no contracted label is silently treated as an original taxon.

## Conditional interfaces

The macro-entry obligation **OPEN-STATE-ORIGINAL** is still required when applying these theorems to the complete state machine: every current source component must carry its exact disjoint original-label set; every surviving original final block must belong to its assigned current component; cuts, contractions and reverse contractions must preserve that assignment and the source agreement relation. The graph theorems accept these objects as explicit original-label inputs. They do not prove an unspecified source history invariant. This obligation is consumed before `findCommon` is called at integration lines 15 or 25.

After a valid original-label state is supplied, the next unproved call is **OPEN-CORE-REALIZATION**, at integration lines 20 and 27–28. For every source-valid monochromatic final refinement F, the real source generator must emit a permitted Q such that F refines Q, each Q block is monochromatic, and an actual nonredundant source cut witness realizes Q at its charged original-edge cost. The generator must preserve budget pruning and prove its mass and total construction work. The theorem `conditional_core_child_preserves_target` at `Composition.lean:38` merely prints the assumed selection interface; it is not evidence for that generator.

The refinement direction is essential: the surviving final partition F must refine the emitted Q. Producing a further refinement of F can increase the final component optimum and does not establish survival at the old budget. `refinement_preserves_avoidance` proves the target geometry only after the correct refinement direction is supplied.

`distinct_parent_cut_cost` proves exact addition for nonredundant cut lists with distinct source-component edge namespaces. This theorem consumes the component membership and nonredundancy premises. It does not construct original-edge lifts or prove their membership. The source implementation must supply those premises and an injective actual original-edge interpretation; same-parent unions have no additive-cost theorem here. The B double clear consumes one joint-color core. The paid count-2 alternative consumes one binary B core, or two cores belonging to distinct source parents A,C.

No recurrence mass, generator coverage, full state termination, remaining source-rule priority, decomposition query, budget iteration or original-forest reconstruction theorem follows from these geometry files alone. The full target's primary milestones remain open in this report. The different organizing choice is to recompute every collision and color in the fixed original target tree while preserving original-label source components, rather than transport suppressed target addresses through history.

## Executed controls

`Controls.lean` checks a proper binary target with three disjoint parent label sets whose three spans have exactly one common vertex and no common edge. It also checks a chain with disjoint endpoint spans, two occupied B targets, and exactly two nonempty joint B leaf regions. These are development controls, not universal evidence. The universal claims above use Lean induction and the executable representation theorem.

`FalseControl.lean` asserts that a singleton leaf avoids itself and that the chain's two joint regions have count three. Lean rejects both with “Tactic `decide` proved that the proposition ... is false.” A separate positive control records that deduplicating two copies of the same source-parent cut gives one edge although adding the list lengths gives two.

No census, numerical oracle, frozen result, integrity pin, or sibling proof file was read or changed. The imported original RMAF model and the target proposal were development contacts. All compilation attempts, including failed elaborations, are retained. Author replay establishes kernel checking of the printed statements; independent verification of hypotheses at the complete algorithm's calls is still pending.
