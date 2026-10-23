# Labelled-family normalization checkpoint

Lean 4.35.0 accepts a universal family normalization in the finite address-tree
model. The result is **awaiting fresh semantic acceptance**. Full G2 remains
open, including transition completeness, merging, and the executable model
interfaces. No unrestricted algorithm or new exponential bound is claimed.

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
normalized open support enters a child exactly when it has a leaf there;
the no-leafless-child corollary forbids assigning or charging such a fragment.
Closed leaf sets are distinct, and each differs from an open leaf set.
`normalized_block_charge` proves that a normalized family's labelled-block
count equals its closed cost plus the 0/1 open-boundary charge.

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

The original normal-form audit retains 31 new declaration inventories: 30
theorems and the `normalize` constructor. The later geometry audit retains 39:
38 theorem inventories and that constructor. The latter includes the former;
do not add the counts. The 27 old core/region dependencies and 16 path-route
dependencies are separately listed and are not new author-family results.
All accepted sources use only `propext`, `Classical.choice`, and `Quot.sound`,
or subsets thereof. The concrete singleton family has closing cost zero; the
false claim that it has cost one fails specifically on `0 = 1`. Its clean
twin and retained-root checks compile.

Commands and exact hashes are in `triple-family-lean-v1.json` and
`triple-family-lean-geometry-v1.json`. The workspace wrapper rebuilds imports
into the continuation's isolated directory. Earlier triple-DP sources and
receipts are unchanged. Failed elaboration attempts are retained; their
`sorryAx` diagnostics were never accepted as proofs. The general BootLoops
package suite was not run by this Lean-only continuation.

The independent path and cost arms did not read the author-family code while
constructing their results. Their work is not automatically an independent
verification of this composition. Fresh semantic, axiom, control, and consumer
review is being performed separately.

## Remaining consuming interfaces

1. Identify the least-hull closed span with the executable RMAF/graph span.
   The executable hull extraction is assigned to the separate bridge arm.
2. Connect this raw/retained representation to the cost arm's finite indexed
   family representation; its three constructors are not yet imported here.
3. Prove universal merge and both directions of four-transition family
   correspondence, including how restriction selects/reindexes live regions.
4. Connect preserved leaf predicates to all good colors/bad masks, instantiate
   the generic automaton, and prove the Python table/backpointer refinement.

The accepted partial target is family normalization in this stated model.
The logical closure definition, shared address semantics, and remaining
interfaces stay explicit; the theorem is not promoted to complete G2.
