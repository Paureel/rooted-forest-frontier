# Labelled-family normalization checkpoint

Universal family normalization in the finite address-tree model has passed
fresh semantic review and an isolated Lean 4.35.0 rebuild. The rooted-path
composition and three assembly operations have also passed fresh review.
The forward transport between the two family representations has passed its
own fresh review. Full G2 remains open, including transition
completeness, merging, and executable model interfaces.

## Objects and theorem

`FamilyModel.lean` defines a finite binary tree by its actual vertex-address
list and its partial address-to-leaf-label map. `LabelledTree` requires
distinct leaf names. `vertex_iff_mem` connects the recursive vertex predicate
to the finite list. The geometric relation is the previously audited
`OnPath` address relation; a separate graph/executable equivalence is not
assumed here.

A `RawFamily t k` has k indexed closed supports and at most one open support.
Every closed support is path convex, lies in the tree, contains a leaf, and
avoids the subtree root. Closed supports are pairwise disjoint. The open
support is path convex, lies in the tree, contains the root, and is disjoint
from every closed support. It may have no leaf. The family covers every leaf.
Thus coverage and disjointness imply unique assignment; they are hypotheses
on the input and proved fields of the constructed output, not hypothesized
properties of the trimming operation.

`Hull L` is defined as the intersection of all path-convex supports containing
L. `hull_contains`, `hull_least`, and `hull_pathConvex` prove its inclusion,
minimality, and convexity. Closed regions use the hull of their leaf vertices.
A leaf-bearing open region uses the hull of its leaf vertices plus the root;
a leafless raw open region is discarded. This definition is noncomputable in
Lean and supplies a mathematical normalization, not an extracted algorithm
or runtime claim.

`normalize` constructs a new `RawFamily t k`, including all its convexity,
tree-membership, liveness, disjointness, root-boundary, and coverage proofs.
`normalization_theorem` specializes this to a finite distinctly labelled tree
and proves retained open liveness, exact per-block leaf preservation, normal
form, unchanged closed cost, and unchanged labelled-block count. Closed cost
is k. Labelled blocks count k plus one precisely when the open support has a
leaf. Discarding a leafless open support changes raw support-object count but
does not change either of these quantities.

`FamilyGeometry.lean` composes the completed, separately authored explicit
path route with the least-hull route. `openHull_eq_rootPaths` proves equality
for nonempty leaf sets. `normalized_open_child_occupied` proves that a
normalized open support enters a child exactly when it has a leaf there.
The no-leafless-child corollary excludes every vertex of a child with no leaf
of that normalized open support. Family restriction and DP charging remain
separate obligations.
Closed leaf sets are distinct, and each differs from an open leaf set.
`normalized_block_charge` proves that a normalized family's labelled-block
count equals its closed cost plus the 0/1 open-boundary charge.

The separately authored `cost_route/FamilyAssembly.lean` uses a complete,
duplicate-free finite index enumeration. Its cost is the number of indices
whose support avoids the root, as proved by `cost_counts_closed_indices`.
It constructs valid families for close-both, extend-left and extend-right.
The corresponding tolls are the sum of both old boundary charges, the right
boundary charge, and the left boundary charge. Every input index survives
with its leaf block; equal colors never identify indices. Universal merge
and the reverse restriction direction are still absent.

`FamilyTransport.lean` proves that the two models use the same actual vertices
and leaf-label map, then defines `toClosedAssembly` and `toOpenAssembly`.
These functions preserve every retained support verbatim, with index types
`Fin k` and `Sum (Fin k) Unit`, respectively. Their block counts are k and
k+1, while both costs are k. `normalized_assembly_exists` constructs an
assembly family from any raw family with exactly its closed cost and labelled
block count. The theorem's concrete witnesses retain the normalized supports;
they need not equal the original raw supports. Its existential statement
exports cost and block-count equalities, while exact support preservation is
available from the two concrete functions. This is a forward representation
map; an inverse and the full transition correspondence are not supplied.

## Input correction and adversarial evidence

The pin says charged regions must contain labels. The old DP note additionally
requires every retained open state to have local labels. The distinction
matters: on tree (a,b), the raw family with closed supports {a},{b} and open
support {root} has three support objects, two labelled blocks, and closed cost
two. Dropping its leafless open support leaves the latter two quantities
unchanged. Treating it as a third charged block is the frozen mutant.

`INTERFACE.md` and the versioned control amendment pin this correction before
the formal model. The original controls remain unchanged: their
`family_valid` field meant retained validity. The misleading original control
ID `charged-leafless` is preserved as provenance; its region at the root is
actually an uncharged open support.

The author control runner passed 14 frozen rows, followed by all three rows
of the raw/retained amendment. The separate X0 checker passed 11 positives and
caught six corruptions with matching clean twins. Its bounded probes admitted
119 family records among 677 supports and discarded 21 raw leafless child
fragments. Those records are not claimed to be distinct unlabelled families.
These are finite controls and regressions, not the universal proof.

## Executed Lean checks and provenance

The original normal-form audit retains 31 axiom queries: 30 theorems and the
definition `normalize`. The geometry audit retains 39: 38 theorem queries
and that definition. The transport audit retains 50: 47 theorem queries and
the three definitions `normalize`, `toClosedAssembly`, and `toOpenAssembly`.
These totals overlap and must not be added. The latest replay separately
lists 60 dependency queries: 27 old core/region queries, 16 path-route queries,
and 17 cost-route queries. The cost-route queries cover 13 theorems and four
family-construction functions; they are not new author-family results.
All accepted sources use only `propext`, `Classical.choice`, and `Quot.sound`,
or subsets thereof. The concrete singleton family has closed-region cost
zero while open. The false claim that it has cost one fails specifically on
`0 = 1`. The transported singleton also has one block and cost zero; its
cost-one mutant fails on that actual false proposition. Clean twins compile.

Commands and exact hashes are in `triple-family-lean-v1.json`,
`triple-family-lean-geometry-v1.json`, and
`triple-family-lean-transport-v2.json`. The workspace wrapper rebuilds imports
into the continuation's isolated directory. Earlier triple-DP sources and
receipts are unchanged. Failed elaboration attempts are retained; their
`sorryAx` diagnostics were never accepted as proofs. The general BootLoops
package suite was not run by this Lean-only continuation.

The independent path and cost arms did not read the author-family code while
constructing their results. The subsequent compositions use their completed
proofs and are not independent derivations. `fresh_review/REPORT.md` accepts
normalization after reproducing all 17 registered rows with a fresh BFS
checker and rebuilding the original 31 queries. Its three supplementary
reviewer lemmas are counted separately. `composition_review/REPORT.md`
accepts the path, geometry, and three assembly interfaces after 16 independent
graph checks, 16 wrong-result rejections, and 17 isolated build stages.
Both reviews limit acceptance to their stated partial interfaces. The later
`composition_review/transport_review/REPORT.md` accepts the forward transport
after two independent fixture controls, two wrong-cost rejections, and 12
isolated build stages. It verifies the actual false transported cost and its
same-import clean twin. Its 11 new queries supplement the earlier 39; they
are already included in the cumulative 50.

## Remaining consuming interfaces

1. Identify the least-hull closed span with the executable RMAF/graph span.
   The executable hull extraction is assigned to the separate bridge arm.
2. Complete the remaining representation direction and prove universal merge
   and both directions of four-transition family
   correspondence, including how restriction selects/reindexes live regions.
3. Connect preserved leaf predicates to all good colors/bad masks, instantiate
   the generic automaton, and prove the Python table/backpointer refinement.

The accepted partial result is family normalization in this stated model,
rooted open geometry, three sound assembly operations, and the forward
normalization-to-assembly representation map. `NEXT.md` states the remaining
universal merge and restriction targets.
The logical closure definition, shared address semantics, and remaining
interfaces stay explicit. No complete G2, unrestricted algorithm, new
exponential bound, or novelty result is claimed.
