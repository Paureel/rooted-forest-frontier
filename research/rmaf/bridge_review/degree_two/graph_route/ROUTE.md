# Graph deletion route, derived after the adversary-first pin

Status: ordinary mathematical derivation, awaiting nonauthor review. The Lean
intermediate is separately reported below. No G3/G4 closure is claimed.

## Definitions and facts read from completed sources

RMAF.lean lines 115–133 keeps unary path vertices in `rootedSpan` and starts
`minimalVertices` at the selected LCA. Lines 144–158 define restricted agreement,
partition checking, and pairwise embedding disjointness. GraphRegion.lean lines
9–14 defines actual parent/child adjacency and finite walks. Its lines 145–157
require a MinimalEmbedding to be least among connected supports containing all
terminals. ExtractorLeastness.lean lines 213–223 proves that exact leastness for
`minimalVertices`. ActualEmbedding.lean lines 9–23 instantiates every original
field; lines 33–45 identifies support and selected occurrences exactly.

All graphs here retain every actual address vertex. Equal addresses in different
trees are not an isomorphism. A selected occurrence is a leaf occurrence, not a
label copied onto an internal vertex.

## G-del: delete a degree-two vertex of the unsuppressed terminal hull

Let H be the exact support of B in t. It is a finite connected subgraph of the
address tree and contains all selected occurrences. Parent/child address edges
form a tree: successive deletion of final bits gives a unique path to the empty
address, and the first differing bit gives the unique path between addresses.
Consequently every connected support contains the unique path between each pair
of its vertices. By leastness H is exactly the union of paths between its
selected occurrences (including the occurrence itself for a singleton).

Suppose v belongs to H and has exactly two neighbors in H. It is not a leaf
occurrence: a leaf in the ambient tree has at most one neighbor, while a
single-vertex tree has none. Deleting v leaves exactly two connected components
C0,C1. Indeed, each vertex other than v has a unique path to v and hence reaches
exactly one neighbor of v without using v; the two neighbors cannot remain
connected after deleting v without producing a cycle.

Each Ci contains a selected occurrence. Otherwise remove that entire component
from H, retaining v and the other component. The remainder is connected and
contains every selected occurrence, contradicting leastness because Ci is
nonempty. Define Bi by the labels of selected occurrences in Ci. Unique labels,
common occurrence of every member of B, and v not being a selected occurrence
make B0,B1 nonempty, disjoint, and a partition of B.

The exact hull of Bi is contained in Ci: Ci is connected and contains all its
selected occurrences, so the completed leastness theorem applies. Thus the two
new t embeddings are disjoint subsets of H and both avoid v. This is the entire
conclusion licensed by graph deletion in one tree. It does not yet prove
restricted agreement or disjointness in u.

## G-prop: propagation from a component label set

Let B be contained in S, both interpreted by selected occurrences in one actual
tree, and suppose H(B) uses v and v is not a selected occurrence for B. First,
H(B) is contained in H(S): H(S) is connected and contains every B occurrence,
so leastness applies. If H(B) had degree zero at v, its connectedness would force
H(B)={v}; its nonempty terminal set would make v a terminal, a contradiction.
If its degree were one, deleting v would leave a connected support containing
all its terminals, contradicting leastness. Therefore its degree is at least
two. Its neighbors are a subset of H(S)'s neighbors. If H(S) has degree exactly
two there, H(B) has exactly those two neighbors. The exclusion of a selected
occurrence is load-bearing; no degree assertion follows for a singleton leaf.

This argument uses no equality of full label sets across trees.

## G-transport: the exact additional mathematical bridge

The two blocks from G-del have the following description in the rooted tree
obtained by suppressing unary vertices of H. Its root is the LCA of B; selected
leaf occurrences and branch vertices are retained. Induction on the actual
tree constructors identifies this rooted labelled tree with `restrict B t`:
no contributing child gives none, one contributing child is suppressed, and
two contributing children retain their binary parent. Paths below a contributing
parent retain all original vertices before suppression. Thus this identification
is between a contraction and a restriction, never equality of address lists.

If v is the root of H, its two neighbors are its two children. Deletion separates
the two child subtrees of the restricted root. If v is not the root, its parent
belongs to H, and degree two means exactly one child belongs to H. Suppression
therefore contracts the chain through v into one edge; one side of that edge has
precisely the selected descendant labels below v, and the other has the complement.
There is a retained branch vertex above that edge (possibly the root), since v
is strictly below the LCA. Both sides contain selected leaves by G-del.

Given `restrictionAgrees t u B`, the completed `sameShape_correct` supplies a
rooted label-preserving isomorphism of these restricted trees. It sends the root
child bipartition or the selected edge bipartition to the same label bipartition
in the suppressed support of u. Expand its corresponding edge (or the two root
branches) back into the original u support. Cutting an edge in that expansion
separates two connected sets containing the B0 and B1 occurrences. Their exact
hulls therefore remain on opposite sides by leastness, hence are disjoint.
Both are subsets of H_u(B), again by leastness.

For each Bi, take the minimal connected subgraph containing its leaves inside
the restricted B trees and suppress its unary vertices. The isomorphism restricts
to these subgraphs because it preserves paths, selected leaves, and the root
order. Suppressing before or after taking the Bi hull gives the same rooted
labelled tree: a suppressed vertex has one surviving child and carries no label,
so contraction only shortens a path; a retained branching vertex survives exactly
when both child directions contain Bi leaves. This constructor/branch criterion
proves the required restriction compatibility here; it is not an assumption of
universal associativity. It yields `restrictionAgrees t u Bi = true`.

This paragraph is an ordinary mathematical transport derivation. Its crucial
formal interface remains to be built: deletion-defined labels must be related
to an edge/root bipartition of the executable restriction, and a rooted
isomorphism must produce disjoint actual u hulls plus restriction agreement of
the two blocks. The graph-only Lean module does not establish that interface.

## G-consumer: actual agreement partition, conditional on full local refinement

Assume P is an actual agreement partition of two uniquely labelled trees with
the same full label set, and B occurs in P. Replacing that occurrence by B0,B1
keeps every block nonempty and preserves the exactly-once flattened label counts.
Their restricted agreements were obtained in G-transport; all other agreements
are unchanged. Every other block's embedding was disjoint from H_t(B) and
H_u(B), so the two subset inclusions preserve those disjointness checks. The two
new blocks are mutually disjoint in each tree. Hence every conjunct of the
unchanged `RMAF.agreement` definition still holds, and list length increases by
exactly one. Any previously avoided marks stay avoided in their own tree by
subset inclusion. Arbitrary splitting is not licensed by this argument.

At the `clearRest` use site, G-prop must first transfer component degree two to
the unique agreement piece using v; G-del plus G-transport repairs it. A state
already avoiding v is retained. Pairwise disjointness makes the using piece
unique. These ingredients address the one-vertex repair only. G2 is still needed
to turn avoidance of this vertex into the full compatibility assertion, and
G5–G7 are not supplied here. Joint marks can still cost more than one cut.
