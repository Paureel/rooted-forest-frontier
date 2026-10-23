# Degree-two final interface review

I confirm the scoped target for the final sources bound by the author replay receipt `7b6cea342c8b72c04907643d7075c5bdd36758950e83d0e10af72732aef3fa43`. I found no defect in the actual two-tree refinement, its original agreement-partition consumer, or the component-to-piece degree propagation. The full `ExchangeSystem` realization, G2, G5–G7, safe cover, runtime and novelty remain open.

I authored none of the proofs under review. Before reading the implementation, I froze the exact inputs and expected results in `FROZEN-CONTROLS.json` and wrote a new checker using leaf addresses and unions of paths between selected leaves. I did not import prior checker code or read the sibling degree-two fresh review. The independent checker and the Lean proofs share the target definitions and fixture inputs; their support algorithms and implementations differ. The finite checks below test the intended semantics, while the universal statements are the Lean theorems with the hypotheses listed here.

## Local theorem

`ActualRefinement.lean:12–40` proves `actual_two_tree_split`. The following table audits every argument in its signature.

| Argument or premise | Meaning and use |
|---|---|
| `t u : Tree` | Arbitrary ordinary binary rooted trees from the unchanged RMAF model. |
| `B : List Nat`, `v : Vertex` | Arbitrary selected labels and one Boolean-list address in the cut tree `t`. |
| `hnt : (leaves t).Nodup` | Unique labels in `t`; used to place every occurrence of a selected label on the same side of the cut. No full-label equality is assumed. |
| `hB : B.Nodup` | No repeated labels in the selected list; both filters inherit this property. |
| `hBt : ∀ x, x ∈ B → x ∈ leaves t` | Every selected label occurs in `t`; supplies the nonempty hereditary restriction step. |
| `hagree : restrictionAgrees t u B = true` | The actual nonempty restrictions are related by `RootedIso`, by `RMAF.sameShape_correct`. |
| `hdegree : actualDegree t B v = 2` | Counts distinct actual parent/child neighbors in the unchanged unsuppressed support and entails membership of `v`. |

The conclusion provides two nonempty duplicate-free lists, a permutation of `B` after concatenation, disjoint labels, agreement of each restricted block, containment of both new supports in the old support in each tree, disjoint new supports in each tree, and avoidance of `v` in `t`. The stronger target assumptions that `u` also has unique labels and that every label of `B` occurs in `u` are sufficient; the implementation needs no separate premises for them. Degree two entails a nonempty support, so the missing explicit `B ≠ []` premise does not weaken the conclusion incorrectly.

I checked the construction in `LocalSplit.lean:199–217`. It chooses an occupied child of `v` and filters `B` by occurrence below that child. Unique occurrence places the first support below the child (`59–71`); the second support stays outside (`73–81`). Both lists are nonempty (`117–150`). If the second support still used `v`, its nonterminal leastness would force two neighbors, hence the chosen child, contradicting its outside property (`174–189`). This reasoning retains the actual path vertices.

`RestrictionTransport.lean:23–51` proves restriction associativity and its subset version from `restrict`. Lines `74–86` prove that rooted isomorphism survives restriction. Lines `108–135` derive agreement for each nonempty subblock. `SupportProfile.lean:55–102` proves the recursive formulas for the actual support-intersection summary. `ActualSupportTransport.lean:38–80` proves that summary invariant under restriction and child swaps; lines `85–110` derive actual disjointness transport. The final local theorem supplies each subset premise from the output permutation. No cut-correspondence, cross-tree address equality, suppression or transport proposition is assumed.

## Partition theorem

`ActualRefinement.lean:44–65` proves `actual_partition_split` for arbitrary `t`, `u`, `before`, `after`, `B`, `v`, and arbitrary mark predicates `mt`, `mu : Vertex → Prop`. Its premises are unique labels in `t`, the original Boolean `agreement t u (before ++ B :: after) = true`, avoidance of `mt` and `mu` by the respective original partitions, and `actualDegree t B v = 2`. There is no premise supplying the desired refinement or any cross-tree transport.

`AgreementBlock.lean:22–30` derives nonemptiness, duplicate-freedom, occurrence in both trees and restricted agreement of `B` from the original whole-partition predicate. `PartitionRefinement.lean:121–144` preserves both original partition checks, every block's restriction agreement, and pairwise embedding disjointness in both trees. The arbitrary `before` and `after` lists preserve all other list positions. Lines `183–216` prove that the other pieces avoid a vertex used by `B`, then clear that vertex from every block of the new list.

The two mark predicates remain in their own coordinates: `AvoidsPartition t ... mt` and `AvoidsPartition u ... mu` are defined separately at `PartitionRefinement.lean:151–159`. Support containment proves their preservation at `161–179`. The final theorem concludes the original `agreement` on the replacement list, no occupant of `v` anywhere in that list, both mark-avoidance predicates, exactly one additional component, and exactly one additional unit of `length - 1`. It does not replace the original agreement definition. For a forest cost `length - components`, the unconditional bound of at most one additional unit is proved separately at `224–229`.

## Component degree

`ActualRefinement.lean:69–87` proves `actual_component_partition_split`. Its tree, partition and mark arguments and premises are those of the partition theorem. It additionally quantifies a label list `S` and requires `B ⊆ S`, actual membership `v ∈ minimalVertices B t`, nonterminal membership `v ∉ terminals B t`, and `actualDegree t S v = 2`. It concludes the same original-partition refinement and count statements.

`DegreePropagation.lean:71–117` derives two distinct neighbors for an occupied nonterminal of a least connected support: deleting a supposed unique-neighbor nonterminal preserves the selected terminals and connectivity, contradicting leastness. Lines `142–171` derive actual support containment, instantiate the prior completed extractor's `MinimalEmbedding`, and combine the lower neighbor bound with the degree-two upper bound in `S`. `DegreeCounting.lean:95–101` converts this to the executable integer degree. The nonterminal premise is explicit at the component entry point and is used. The local split itself derives nonterminality from its own degree-two premise (`LocalSplit.lean:110–115`).

## clearRest interface

The unchanged consumer is `PureBridge.lean:79–80`:

```lean
clearRest : ∀ r, restValid r → ∃ r', restValid r' ∧ restAvoids r' ∧
  restCost r' ≤ restCost r + 1
```

Its only call is in `paid_replacement`, line `115`, with the original state's `restValid` proof. The new actual partition theorem provides the needed one-piece repair when the selected occupied piece meets the degree assumptions. A partition already avoiding the vertex can remain unchanged; if it uses the vertex, pairwise disjointness allows at most one occupying piece and the replacement clears the whole list. These are the scoped G3/G4 ingredients. A concrete interpretation of the entire remainder as `R`, proof of the degree premises for every relevant valid state, and construction of all fields of `ExchangeSystem` remain necessary. This review does not promote a theorem with explicit piece/degree premises into an arbitrary universally quantified `clearRest` field.

`PureBridge.lean:75–78` still requires compatibility and collision properties, and `FORMAL.md` separately lists G2 and G5–G7. The degree-two refinement does not establish those properties, the role-swap equivalence, an elimination algorithm, or additive mark penalties.

## Executed evidence

| Check | Result and retained evidence |
|---|---|
| Frozen independent exact controls | All 47 checks passed; `independent-results.json`. Root degree 2, path degree 2 with `[false]` retained, unequal outside labels accepted locally, quartet partition 3 → 4 components, and degree-three avoidance minimum 3 pieces. |
| Planted semantic corruptions | Wrong degree, missing path, substituted cross-tree address, wrong root, overlap and unchanged component count were rejected with clean controls. Empty/singleton and absent/repeated-label premises were checked. |
| Joint marks | Fresh enumeration recovered exact additional-cut optima `[1,1,1,2]` from the prior frozen data, rejecting additive increments. |
| Isolated Lean rebuild | All 24 pinned source modules rebuilt from source in `isolated/`, with `LEAN_PATH` limited to that directory; `rebuild-receipt.json`. The dependency order was reconstructed from imports. |
| Axiom inspection | Each manifest declaration occurred exactly once in the fresh 210 printed-axiom reports, with only `propext`, `Classical.choice`, `Quot.sound` or no axioms. Independently parsed named source declarations matched the manifest. These are coverage counts, not a new theorem inventory. |
| False Lean controls | All 16 author semantic false propositions failed with explicit `decide` falsity. I also compiled the exact negation of each as a positive twin: all 16 passed; `audit-receipt.json`, `twins/`, `logs/`. |
| Malformed control | The separate wrong-type file failed with a type mismatch, and its clean twin passed. It contributes no semantic rejection evidence. |
| Source integrity | Every author receipt/source/log/script pin matched. The seven shared dependency sources also matched the completed leastness checkpoint. All source pins matched again after rebuilding. |
| Circularity and bypass scan | The source import graph is acyclic and terminates in `Std` plus the permitted prior sources. Comment-stripped pinned sources contain no `axiom`, `sorry`, `admit`, `native_decide`, `unsafe`, or `implemented_by` token; `audit-receipt.json`. |

The standalone review scripts are `exact_check.py`, `rebuild.py`, `audit.py` and `finalize.py`; run them with `./bootloops-python`. They use `./bootloops-lean` for formal checks. Original proof files and existing verification records were not edited. The unique copies in `inputs/` retain each executed source even where different original directories use the same filename. Expected false-proof attempts and their logs remain available.

I did not run the project-wide `./bootloops-check`, a larger search, or a literature review. No shared toolkit code changed. The verdict concerns the universal executable-model statements above, their explicit hypotheses, the original partition use site and the independently reconstructed finite semantics. It makes no runtime, full-exchange or novelty claim.
