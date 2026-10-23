# Source work and representation v1

The executable routine is `ForestPretest01.pretest01 T ss`. It uses the
original `ForestState.proper`, `ForestState.agrees`, and
`ForestState.additionalCost`; it enumerates no label assignments or set
partitions and calls no optimum oracle. Candidate generation recursively
visits every literal current source tree. For each nonroot original vertex
address p of that tree, it replaces that tree's one leaf block by the
subtree-label block and its complement, retaining every other source block.
The unchanged full source-label partition is also tested. Repeated label
partitions from distinct original edges remain as separate candidates.

`candidates_count` proves that the number of candidates equals one plus the
sum of the numbers of original edges over all current source trees.
`edges_leaves` proves E(s)+2=2|leaves(s)| for each binary tree.
`candidate_linear_bound` proves a bound of 1+2n, where n is the total number
of current source leaves. All checks use the entire candidate, so target
hulls shared by different current source components remain visible.

Let N be the total number of target/source tree vertices plus the number of
list cells in the input representation, and let B be one plus the maximum bit length
of an original natural-number label. Count list constructors, traversals,
Boolean branches, address bits and bounded-word indices as source
primitives. Leaf and vertex lists have polynomial size in N; stored vertex
addresses have length at most N. Restriction and rooted/minimal span
construction recurse over input trees and use finite list membership.
The `sameShape` recursion visits pairs of input subtree roots, at most the
product of their vertex counts. Pairwise clearance compares finite lists of
addresses; partition checks count labels in a finite flattened candidate.
These facts give polynomial source work for one full agreement check and
hence for all O(n) candidates. The proof modules certify the exact candidate
count and semantic coverage. They do not contain a formal instruction-count
bound for every original `agrees` primitive.

The primitive model charges a label comparison as one operation only when
labels fit a bounded machine word. With arbitrary `Nat` labels, label
comparisons incur a factor polynomial in B; addresses and list indices also
have their actual bit lengths. A full candidate has at most n+1 nonempty
blocks on proper accepted inputs, contains each of the n input labels once,
and carries their original values. Its label payload therefore requires
O(n B) bits, plus list/block and index overhead. Candidate enumeration may
retain O(n) such forests. No constant-cost arbitrary label, compact label
encoding, compiled-code runtime, or unconditional parent source bill is
asserted.

The source reconstruction theorem uses the frozen ordinary
`DepthOne.source_two_split` as proof support. Its production-core machinery
is erased from the executable entry point. The pretest contains no
noncomputable definition and no desired-coverage/minimum record.
