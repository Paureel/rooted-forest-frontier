# Edge-separation derivation

This is an ordinary mathematical derivation of the proposed statement. Only
the finite source equalities listed in results/lean-checks.json were checked
by Lean in this arm; the universal steps below remain proof obligations for
the constructor and its fresh reviewer.

## Objects

Let t be an actual finite RMAF.Tree and S a list of natural-number labels.
Construct its incidence graph recursively: a leaf has one vertex; a node has
its root, disjoint left/right copies of the child graphs, and one edge from
the root to each child root. Identify each vertex with its root-to-vertex
Boolean address. Appending one Boolean traverses a child edge. The ambient
list is the recursive preorder enumeration of all these valid addresses.

Let T be the set of leaf *occurrences* whose labels belong to S. An occurrence
is a vertex, so repeated labels at different leaf addresses give different
members of T. For each graph edge e, delete e and denote the two resulting
components by A_e and B_e. Let F contain exactly those edges for which both
T ∩ A_e and T ∩ B_e are nonempty. Define K as T together with every endpoint
of an edge in F.

The valid-address graph is a finite tree by induction on t: the two child
graphs are disjoint trees, and each is joined to the new root by exactly one
edge. Removing any edge therefore produces exactly two components. The
definitions of Adj and Walk agree with this graph when every walk vertex
belongs to the ambient list (GraphRegion.lean:9–14).

## Forced vertices

Suppose P is a connected ambient support containing every member of T.
For e ∈ F, choose a ∈ T ∩ A_e and b ∈ T ∩ B_e. Terminal inclusion puts a and b
in P, and connectedness gives a finite P-walk from a to b. Ambient inclusion
places every vertex of that walk in the valid-address graph. Along the walk,
the first step leaving A_e must traverse e: every other graph edge remains
after e is removed and consequently has both endpoints in one component.
Both endpoints of e belong to P. Every terminal belongs to P by hypothesis,
so K ⊆ P.

This argument uses every competitor condition in MinimalEmbedding.minimal:
ambient inclusion prevents a walk from leaving the incidence graph;
terminal inclusion supplies vertices on both sides of each separating edge;
connectedness supplies the walk. Duplicate entries in the competitor's list
do not alter its vertex-membership predicate.

## Source recursion

The auxiliary rootedSpan recursion admits the following direct induction:
its output is empty exactly when the subtree contains no selected occurrence;
otherwise its members are exactly the subtree vertices with at least one
selected occurrence below them. At a leaf, both assertions follow from the
contains branch. At a node, the two empty outputs produce an empty list;
otherwise the source includes the current root and the two prefixed child
outputs (RMAF.lean:116–122). The child vertex sets are disjoint, and neither
contains the current root, so the induction also proves ambient validity.

Induct on t to identify the membership set of minimalVertices S t with K,
using the unchanged branches at RMAF.lean:126–133:

1. At a leaf, a selected label gives its unique occurrence and no edges;
   an unselected label gives the empty set.
2. If neither child contains a selected occurrence, T and F are empty.
   The source takes its empty-left branch and recursively obtains an empty
   right result. Both sides are empty.
3. If only one child contains selected occurrences, every selected occurrence
   lies in that child. Neither root-child edge separates terminals, and no
   edge in the other child does. For an edge inside the active child, whether
   terminals meet both sides is the same in that child and in the whole tree.
   Thus K is the prefixed child K. The source takes exactly the corresponding
   one-sided branch; the current root is absent.
4. If both children contain selected occurrences, both root-child edges
   separate terminals. For an edge inside either child, its component away
   from the current root contains a selected occurrence exactly when the
   descendant endpoint is in that child's rootedSpan. The component toward
   the current root contains a selected occurrence in the opposite child.
   The endpoints of all such edges, together with the terminal occurrences,
   are the current root and the two prefixed rootedSpan sets. The source's
   final branch returns exactly these vertices.

These cases prove ambient inclusion and preservation of all selected leaf
occurrences without label uniqueness. They also exclude every unselected
leaf: such a vertex is not a terminal, and deletion of its incident edge
leaves no terminal on its singleton side. Repeated entries in S have no
effect because the source tests only List.contains membership.

## Constructor conditions

Assume T is nonempty. Then K contains a terminal and is nonempty. The audited
executable connectivity theorem may supply connectedness of the unchanged
minimalVertices list, provided its nonempty-selected-occurrence hypothesis
is discharged for these exact t and S. Alternatively, for two vertices of K,
the unique tree path between them lies in the subtree spanned by T: each
edge on that path separates terminal occurrences and belongs to F. The
forced-vertices argument then proves the required subset leastness for
every connected ambient support containing T.

For exact leaf/label correspondence, define the partial lookup that follows
an address through t and returns a label precisely when it ends at a leaf.
Induction on t and the address proves: an address occurs in the selected
occurrence list iff the lookup returns some x with x ∈ S. The empty address
at a leaf is included; an attempt to descend through a leaf is invalid.
Internal addresses have no leaf label. This is an occurrence correspondence,
with no claim that x determines a unique address for arbitrary Tree.

An RMAF.Instance separately requires leaves t to permute List.range n
(RMAF.lean:19–24). Since List.range n has no repeated entries, each occurring
label then has exactly one leaf occurrence. The constructor for arbitrary
t must establish occurrence inclusion first; Instance uniqueness may be
used later to derive a label-to-address bijection on the occurring labels.

Empty and absent selections yield an empty source list but do not satisfy
MinimalEmbedding.terminal_nonempty. For the root-leaf tree with a selected
label, both T and the support are the singleton empty address, and leastness
follows directly from terminal inclusion. The ambient and terminal lists
must be explicit source functions with lookup proofs; caller-supplied lists
with asserted target properties would not discharge the target.

## Hypothesis use

| Condition | Where used |
|---|---|
| Actual finite Tree t | Builds finite acyclic incidence graph and recursive address lookup |
| Ambient is exactly all valid addresses | Identifies the graph for edge deletion; discharges inAmbient |
| Adj appends/deletes one final Boolean | Identifies walks with incidence edges, preserving source address orientation |
| Terminals are exactly every selected leaf occurrence | Source recursion, terminal preservation, leaf correspondence; repeated labels remain distinct vertices |
| At least one selected occurrence | terminal_nonempty and a first vertex for ConnectedSupport |
| Other support is connected | Walk between terminals in opposite edge-deletion components |
| Other support lies in ambient | Every walk step belongs to the actual finite incidence graph |
| Other support contains all terminals | Supplies both endpoints' witness terminals and singleton leastness |
| Source rootedSpan/minimalVertices definitions unchanged | Inductive identification of source support with forced vertices K |

No restriction/suppression transport between trees, triple-family theorem,
pure-bridge exchange property, complexity bound, or novelty statement follows
from this argument. The source constructor and its composed consumer call
remain separate universal Lean checks.
