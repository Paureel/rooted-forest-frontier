# Nonauthor pair-case review

I confirm G and E at the statements in TARGET-v1, including executable
original-tree selection and actual agreement-partition surgery. I also compiled
a direct interface from G's returned edge to E. This conclusion rests on the
source-bound universal proofs, their complete declaration audits, and the
semantic argument below. The finite comparisons test the interpretation of
those statements; they do not prove universality. The complete algorithm,
correctness, smaller-base bound, and residual-source operations remain open.

## G derivation

The actual minimal embedding is the union of original leaf-to-leaf paths,
including singleton vertices and all unary path vertices. The common frozen
Bridge proves this equivalence at `minimalVertices_correct:270`; it proves
pairwise Boolean disjointness at `executable_pairwiseEmbeddings:450`.
`selectedLeaves` identifies only labelled original leaves, while `region`
assigns the two descendant directions and the upward direction. A leaf at the
removed vertex has the separate value 3; the proof excludes that case before
counting regions. The original root has no upward component.

At a common embedding vertex, neither parent has a selected leaf there because
their label sets are disjoint. Each parent therefore occupies at least two of
the three directions. The two direction sets meet, and the corresponding
original neighbour lies in both embeddings. The chosen adjacent pair is an
original finite-tree edge: its endpoints belong to minimalVertices, hence to
the original vertex list, and `child_actual_edge` proves edge membership.
Both parent selections have leaves on both sides of that edge.

Suppose one sector still meets the other whole parent embedding. Two sector
leaves witness the collision, and a leaf on the opposite side supplies a third
leaf. Their three pairwise paths and the other parent's convex embedding meet
pairwise. The four-set Helly argument produces a common vertex of all four.
The three leaves lie in three distinct directions at that vertex; none equals
the vertex because a shared selected leaf was already excluded. Thus a sector
collision gives a shared three-region vertex. If that alternative is absent,
the shared edge satisfies both whole-parent mutual-clear conditions. This
argument is in `Selector.lean:112,256,482`; neither clearance nor a selector is
assumed as an input field.

The executable `choose` at line 554 first checks the literal original-label
conditions, then scans actual vertices and edges. Its soundness and completeness
theorems at lines 614 and 634 refer to the predicates just described. The
two-region theorem at line 916 rules out a vertex result. The actual distinct
neighbour count agrees with occupied regions at line 778, and line 834 proves
that the filtered neighbours are exactly original adjacent embedding vertices.
The count of candidate predicate calls is separate from the cost of evaluating
those predicates and from the full solver's runtime.

## E derivation

For an arbitrary agreement F refining proper source partition P, every F block
has a unique parent. The proof groups the blocks into U inside A, V inside B,
and unchanged W. Proper partition counts prove that U partitions A, and the
grouped list is a permutation of F. The output is whole A, followed by the
nonempty descendant/non-descendant pieces of each V block, followed by W.
No enumeration of F occurs in the universal construction.

For each final agreed C in V, the selected leaves under the original target
subtree form a rooted cluster after restriction. Rooted labelled isomorphism
of the restrictions transfers this cluster to the source restriction; lifting
through suppressed unary vertices gives a cluster relative to C in the
original source. Induction on that cluster proves separation of the true
minimal embedding from the false rooted span, so it retains original paths.
This is `Cluster.lean:19,65,110,160` followed by
`Descendant.lean:122`. Every nonempty split piece retains rooted agreement by
restriction. Only final C requires agreement here; the whole parent B does not.

Two mixed V blocks would both occupy the target edge's child vertex, contrary
to F's actual embedding disjointness. Hence splitting V adds at most one block.
If one is mixed, the two A sectors must lie in different U blocks: a mixed U
block would occupy that same vertex. Merging U into A therefore pays for the
possible extra split. If no V block is mixed, the nonempty U already suffices.
This proves the count inequality in `Count.lean:26` without a whole-B cut claim.

Source P's disjointness permits merging A beside B pieces and W. Bilateral
target clearance gives the required separation from split B pieces, and
other-parent clearance separates A from W. Subset monotonicity preserves all
remaining separations from F. `Surgery.lean:39` proves both partition checks,
all rooted restriction agreements, and source/target pairwise embeddings.
`Exchange.lean:88` assembles these facts for every F, proves A occurs once,
proves every B output block lies on one side, and preserves the exact W list.
The retained unused premises are harmless stronger assumptions from the pin.

`SourceEdge.lean:54` constructs an original source edge only for a mixed agreed
final C, with the colour equivalence quantified over C. The subtree may contain
other labels. This statement does not authorize one cut separating the entire
unagreed B or establish an emitted residual operation or its budget charge.

## Consuming trace

| Required interface | Nonauthor ruling |
|---|---|
| Original binary trees and distinct/equal labels | Tree constructors enforce binary shape. G's executable properInput checks original leaves and selections; E states source/target Nodup and label-set equality explicitly. No restriction edge replaces an original edge. |
| Empty, singleton, absent, repeated, or shared selected labels | Original raw semantics and executable proper-input guards are kept separate. The frozen controls and released kernel controls exercise each refusal or boundary behaviour. |
| Nonlabel shared vertices and original root | Derived from actual overlap and disjoint selected labels; upward root region is absent. The degree theorem explicitly requires an occupied nonlabel vertex. |
| Four nonempty descendant sectors | G's two Boolean sides are exact original descendant filters. Both sector lists are nonempty; E's mixed predicate is equivalent to these two witnesses. |
| Full clearance of both parents | G's ActualClear quantifies each sector against the other whole embedding. All four E Disj premises follow through the actual minimalVertices/Hull bridge. The one-sided false controls reject either omitted half. |
| Proper source P and source disjointness | E requires the original partitionCheck and pairwiseEmbeddings tests. G supplies neither and the adapter leaves both as explicit caller premises. |
| A/B distinct parent membership | E's A∈P, B∈P, A≠B remain explicit in the adapter. Parent label disjointness and U's partition of A are derived from proper P and refinement. |
| A-only rooted homeomorphism | E assumes restrictionAgrees S T A; sameShape_correct identifies rooted labelled isomorphism of suppressed restrictions. Whole-B agreement is absent and is false on T1. |
| Every F and refinement direction | F is arbitrary with original agreement and Refines F P, meaning each F block is contained in a P block. No optimum, selected F, or existence premise replaces the quantifier. |
| Actual Fprime and outside/count conclusions | Universal E proves all original agreement constituents, A count one, all B blocks monochromatic, nonincreasing length, and exact outside-list equality. Actual-definition comparisons test these conclusions for every eligible finite F/edge pair. |
| G edge → E subtree and descendant labels | New review-only Interface.lean proves original vertex/treeAt existence, descendant-membership equivalence, exact yes/no filter equality, and all four clearance implications, then directly applies E. All author proof bodies remain identical. |
| Final-C source edge → residual source operations | Remains open. C agreement and source-label membership are essential. Neither this review nor either target proves original-state history, source generation/coverage, cut charging, reconstruction, or full runtime. |

The joint copy imports Selector and SourceEdge with their exact source bodies;
the common RMAF/Geometry/Bridge copies have identical hashes. No module rename
was needed. The two different Controls modules remain unchanged in separate
isolations. A generated declaration `VertexGeometry.Prefix.eq_1` is attributed
to Descendant in the E-only import and Selector in the joint import. The
declaration is present and audited in both; this explains the joint Descendant
count of 23 instead of 24. The complete joint inventory contains 961 declarations,
including nine originating from the six review interface theorems.

## Executed evidence

Fresh source-only G and E builds reproduced all 759 and 766 originating
declarations. Their transitive axiom sets contain only propext, Classical.choice,
and Quot.sound, with no unsafe declaration or local axiom declaration. The
audits include private and generated declarations, not only exported theorem
names. Source-token scans found no sorry, admit, native_decide, or axiom in the
scientific modules. Own clean/explicit-False controls and unused/private/imported
custom-axiom controls ran before candidate compilation. All five affected own
plant declarations were rejected. The ten released semantic-false propositions
also failed with the expected decide-false diagnostics. Replaying the released
custom plants with the fresh auditor rejected G's three and E's two affected
declarations, while the clean twin passed.

The immutable own 43 controls were replayed after release with 43 comparator
mismatches rejected. Actual frozen Lean definitions then matched the independent
pre-candidate graph code on 1298 original partitions, 544 selected hulls, 3896
region/degree values, 7452 actual selector outputs, and all 46 eligible actual
exchange outputs. The common-input and shared-kernel dependencies are recorded;
no author Python checker or runner was used. T1's two minima of five remain
restricted to refinements of its P. The three-region probe remains outside E
and true for the tested existential exchange; it is not a false plant.

One own readout attempt failed to compile because its JSON serializer received
a Prop rather than a Bool. I preserved that source, log, and failed result,
changed the serializer to use decide, and reran all four readouts successfully.
No expected value, proof body, or acceptance threshold changed. Eight additional
post-release corrupted readouts were then rejected by the exact retained
comparator, with the clean twin passing. Those supplementary controls do not
receive pre-candidate preregistration credit.

All work stayed local. No broad toolkit suite, large-label census, author
contact, subagent, remote computation, upload, or hosting was used. The full
algorithm's live implementation and assembly sources were outside the released
review scope and were not inspected; acceptance here is confined to TARGET-v1
G, E, and their proved interface.
