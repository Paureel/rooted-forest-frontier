# Family normalization review

The raw-to-retained normalization theorem is acceptable in the finite binary
address model. It preserves the closed indices, every closed leaf-vertex set,
and the open leaf-vertex set; a leafless raw open support disappears without a
charge. Full G2 remains open: this review does not establish transition
restriction/assembly, graph or executable hull correspondence, color/mask
decoding, or Python refinement.

## Executed checks

The separate `direct_controls.py` implementation reproduced all 17 registered
rows from `controls.json` and `controls-amendment-v2.json`. The checker builds
undirected adjacency from the nested tree, finds paths by breadth-first search,
and forms spans by path union. It checks exact supports and leaf blocks. The
raw-empty-open row has closed cost 2 and two labelled blocks before and after
pruning, while its number of support objects decreases from 3 to 2. The stem
mutant is nonconvex and its complete-stem twin is convex; both incorrect empty
charges disagree with the registered values. The comparator rejected a planted
singleton charge of 1 and accepted its clean charge of 0 before the registered
rows ran. These are finite registered controls, including known regressions;
they are not a holdout census or a proof about the Python solver.

The source snapshots in `source/` match the hashes in
`results/triple-family-lean-v1.json`. The two dependency snapshots additionally
match `results/triple-dp-connected-lean.json`. With Lean 4.35.0 and the workspace
`ELAN_HOME`, every positive module rebuilt into `fresh_review/build/` under a
review-only `LEAN_PATH`. The replay returned 31 family axiom-query results:
30 theorem queries and one query for the definition `normalize`. The 27 dependency
queries are separate. Every reported axiom belongs to `propext`,
`Classical.choice`, or `Quot.sound`; the scanned sources contain no `sorry`,
`admit`, `native_decide`, or declared `axiom`. These counts describe explicit
axiom queries, rather than all declarations in the files.

`NegativeFamily.lean` failed at line 7 with the diagnostic below. The matching
`CleanFamily.lean`, which changes the goal to the correct zero charge under the
same imports and compiler configuration, compiled successfully. The negative
run failed on the proposition itself, with no missing-module or
unknown-identifier diagnostic.

```text
error: Tactic `decide` proved that the proposition
  0 = 1
is false
```

The review also compiled `ReviewSemantics.lean`. Its three theorems prove that
different closed indices cannot have identical leaf-vertex sets, an open
leaf-vertex set cannot equal a closed one, and an empty raw open disappears
while closed cost remains `k`. These are supplementary reviewer statements;
they are excluded from the author's 31 family queries and the 27 dependency
queries.

## Semantic audit

The following locations refer to the retained snapshots under `source/`.
Each quoted fragment was checked against those source bytes. Interpretive
claims are distinguished from the formal statements in the final column.

| Question | Source and exact fragment | Review result |
|---|---|---|
| Are the family hypotheses circular? | `FamilyModel.lean:144`: `structure RawFamily (t : BTree α) (k : Nat) where`; lines 147–156 list convexity, containment, nonempty closed leaf sets, root exclusion, disjointness, and leaf coverage. | No circular conclusion occurs in the fields. They describe admissible input families. `FamilyTrim.lean:50` constructs a new family and supplies every field, using hull containment for disjointness and leaf preservation for coverage. No normalization, transition, or cost theorem is assumed. |
| Is the tree actually finite and labelled? | `TripleDP.lean:10` declares the inductive `BTree`; `FamilyModel.lean:14` defines the finite vertex list; line 39 proves `vertex t v ↔ v ∈ vertices t`; line 37 requires `(names tree).Nodup`. | The syntax is a finite full binary tree. Vertices and labels are computed recursively from that tree. The formal vertex-membership theorem witnesses finiteness. No separately formalized graph object is used. |
| Is the hull genuinely least and convex? | `FamilyModel.lean:85` defines `Hull`; lines 88, 92, and 97 prove seed containment, leastness, and `PathConvex (Hull seeds)`. | Yes, for the audited address-path relation. Intersection is a definition; its required properties are proved. Hulls stay inside the original supports by lines 111 and 114, so they cannot acquire vertices outside the finite tree. Equality with executable path union is a separate obligation. |
| Are labels and exact coverage preserved? | `FamilyTrim.lean:100` states `LeafSet t ((normalize F).closed i) = LeafSet t (F.closed i)`; line 104 states the open membership equivalence; lines 88–92 prove coverage. | Yes, at leaf-vertex addresses. Coverage plus closed/closed and open/closed disjointness gives exactly one region per leaf. The label function is unchanged. A separately named theorem translating vertex sets to finite sets of label values is absent from the reviewed files. |
| Is empty-open pruning free? | `FamilyTrim.lean:9`: `if HasLeaf t R then some (OpenHull t R) else none`; `FamilyModel.lean:161`: `def closedCost (_ : RawFamily t k) : Nat := k`. | Yes. The option becomes `none`, the closed index type stays `Fin k`, and the cost equality is proved at `FamilyTrim.lean:109`. The raw support-object count is deliberately not preserved. |
| Does block count count real blocks? | `FamilyTrim.lean:125` defines `labelledBlocks`, with line 127 `exact k + if OpenHasLeaf F then 1 else 0`; `FamilyModel.lean:149`, 151, and 155 impose nonemptiness and disjointness. | The Lean equality preserves this explicit count definition. Its interpretation as the number of distinct nonempty leaf-vertex blocks is justified by nonemptiness/disjointness; the two injectivity/separation facts are also proved in `ReviewSemantics.lean`. A formal finite-set-cardinality equivalence is not among the author's audited statements. Distinct labels are required by the public `LabelledTree` wrapper, although the normalization proof itself needs only leaf addresses. |
| Can same-color neighbors be merged accidentally? | `FamilyTrim.lean:51`: `closed := fun i => ClosedHull t (F.closed i)`; lines 136 and 153 transport predicates of each leaf set. | No merge operation occurs. Closed indices are retained and supports only shrink. Arbitrary leaf-set predicates are preserved, but actual color assignments and six-mask decoding are not implemented by these modules. |
| Is the theorem merely the desired conclusion hidden in a structure? | `FamilyTrim.lean:164` states `normalization_theorem`; its witness at line 172 is `normalize F`. | No. The input is an arbitrary admissible raw family, and the constructed witness has the least-hull normal form, retained-open property, and preserved leaf sets. The conclusion is a genuine universal normalization lemma within the stated model. |

## Remaining interfaces

Path union and open-stem geometry still require a correspondence theorem for
this logical hull in the files reviewed here. Translating address vertices and
leaf blocks to the executable RMAF representation requires explicit maps and
proofs about minimal spans. The separate path and cost routes were deliberately
not read, imported, or credited by this review.

Full G2 also requires family restriction to child subtrees, assembly through
each of the four transitions, and the exact charge when an open child becomes
closed. These arguments must preserve disjointness, coverage, leaf-bearing
charged blocks, and empty-fragment pruning. The single-region decomposition
in `ConnectedRegions.lean` supplies only its stated local path properties.

G3 requires color and mask decoding, admissibility of assembled label blocks,
the particular min-plus-rule instance, and refinement of Python tables and
backpointers. The generic theorem in `TripleDP.lean` does not supply those
connections. No unrestricted-rMAF correctness claim, new exponential base,
or novelty claim follows from normalization.

## Provenance and reproduction

`FAMILY-TARGET.md` was the first task source read. The checker was written,
executed, and pinned in `pre-author-read.sha256` after reading the interface
and frozen controls, before reading the author implementation. Shared material
consists of the semantic specification and registered fixtures; no author
checker or RMAF helper is imported. The Lean replay uses the same kernel and
the same proof sources, so it is an independent rebuild and semantic review,
not an independent derivation of the theorem. The tiny graph replay supplies
separate finite semantic evidence and does not replace kernel checking.

Run the checker from the workspace root with `./bootloops-python
research/rmaf/triple_dp/family/fresh_review/direct_controls.py --out
/tmp/triple-family-fresh-direct-controls-replay.json`. `rebuild.py` preserves
its original receipt and snapshots by refusing to overwrite them; its receipt
lists the exact Lean commands for a further rebuild into another directory.
The main evidence is in `results/triple-family-fresh-direct-controls.json`,
`results/triple-family-fresh-lean.json`, and `fresh_review/logs/`. No broad
package suite or larger family census was run for this review.
