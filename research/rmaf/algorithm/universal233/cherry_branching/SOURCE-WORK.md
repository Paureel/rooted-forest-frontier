# Source-operation scope

The local selector, original cut construction, and literal child materializer
have polynomial source work in the two original tree sizes. This is an
inspection argument for the pinned executable definitions. Lean checks source
semantics, exact paid costs, and budget identities. No extracted machine-level
or formally metered polynomial bound is claimed here. Fresh nonauthor source
cost review is pending.

Let N be one plus the total number of constructors of T and S, n their common
leaf count, and L one plus the maximum original-label bit length. Every
original address has at most N Boolean cells. All original vertex lists,
minimal embeddings, and rooted spans contain at most N entries. Each actual
pendant list has at most N entries and contains distinct incomparable original
child addresses. Their subtree leaf lists are disjoint in the source graph;
all lists materialized below contain polynomially many cells.

Count constructor allocation, matches, field access, reference copies, Boolean
tests, and scalar operations as unit source operations. Address comparisons
and list construction/copying count all inspected or copied cells. This
convention matches the completed source-work packages. Scalar comparisons gain
a polynomial factor in L and budget bit length when converted to bit work.

Conservative full-scan bounds, allowing every recomputation in the literal
source, are:

| Executable operation | Source upper order | Included work |
|---|---:|---|
| `cherries T` | O(N^3) | Visits every constructor, maps original addresses, appends both sublists |
| `vertices S`, one original leaf search | O(N^3) | Original address allocation, failed find candidates, subtree lookup and leaf comparison |
| one `rootedSpan` | O(N^3) | Membership masks, recursive lists, all intermediate prepends/appends |
| one `minimalVertices` | O(N^4) | Recomputed rooted spans at every constructor, all original vertices before suppression |
| one `cuts S a b` | O(N^6) | All N candidate child addresses, both literal minimal-embedding recomputations per candidate, dropLast and both address-membership scans |
| all `candidates T S` | O(N^7) | Every target cherry and its full rejected/accepted source edge scan; no first-success shortcut |
| priority scans | O(N^3) | Common/t1/high failed candidates, length traversals, final head selection; candidates were already fully materialized |
| one `pendantPartition` | O(N^4) | Every subtreeLabels lookup, every leaf-list append, map/flatten allocation, root-complement masks with repeated flatten evaluation |
| one sourceForest | O(N^4) | Up to N+1 restrictions, whole source traversal and linear selected-list scans; all retained tree constructors are allocated |
| both endpoint branches | O(N^4) | Both actual original terminal searches, singleton/complement lists and materialized forests |
| `remaining`, literal branch construction | polynomial | All budget comparisons/subtractions, reference/field/list construction and all refused child calls |

Their sum is O(N^7) under the source convention, with a polynomial scalar-bit
factor O(L+log(k+2)). A looser O(N^8) envelope may be used in a larger proof.
Input validation, if performed at this boundary, checks both original leaf
lists' distinctness and equal label sets in polynomial work and fits the same
envelope. The conditional child solvers' own work remains separate.

Proof-only surgery (the existential t1 replacement and its common-cherry
coarsening) does not execute inside the branching algorithm. Executable t1
calls the pendant child alone, or the requested two cost1 children. Executable
high calls two endpoint children and one pendant child at costs (1,1,t).
Neither the proof-only split nor suppressed display edges add paid cuts.

After the complete solver selects original G, final source-certificate
recovery runs once. The completed final recovery package proves a source
charge polynomial(N,L)*2^(|G|-1), including rejected prefix work and actual
list/color materialization. Its own helper-versus-fine-operation qualification
remains in force. No theorem here pays for choosing G, absorbs recursive
solver work, or proves a full exponential base.
