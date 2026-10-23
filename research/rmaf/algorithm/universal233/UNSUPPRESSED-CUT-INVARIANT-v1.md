# Original-component route for the core simulation

Status: proposed proof route, OPEN. This note was developed without reading
unfinished integration code. It states what must be proved about the actual
`CoreProgram` calls; it supplies no assumed coverage theorem.

Keep the original source graph and every degree-two/root path. At a prefix,
the actual original cut edges divide it into one leafbearing component for
each detached group and one live leafbearing component L. Its display is the
current grouped skeleton. Each skeleton node's original address p is valid,
and its expanded payload is exactly the live original labels below p.
A normalized leaf group displays a connected pendant region of L, whose only
connection to its complement is the actual original incoming edge at p.
Previously detached descendant groups are holes outside L.

## Cut induction

The attempted chosen group has nonempty payload, nonroot valid original
address p and at least one other live group. Its original incoming edge is
inside L. Deleting that edge separates exactly the chosen live payload from
the other live labels; all old detached components are unchanged. Both new
parts contain labels. Hence exactly one leafbearing component is added and
no leafless component is created. Unary/root suppression affects only the
skeleton display and leaves the original component L intact.

A useful equivalent leaf invariant is the cut signature: original leaves
x,y have the same current component iff every recorded incoming address p
is an ancestor of x exactly when it is an ancestor of y. A new cut splits
only the live signature class. Old detached groups lie wholly inside or
wholly outside the new original subtree; no future selected address is
strictly inside a previously erased group. This should identify the emitted
expanded blocks with actual original components and prove nonredundancy.

## Pure-region coarsening

For a valid monochromatic partition supported in L, take a pure pendant
region U displayed by one normalized group. At most one partition block
containing a leaf in U can also contain a leaf outside U: two such connected
supports would both use U's boundary. Merge every block touching U into the
one crossing block, or into a new U block if no crossing block exists.
All affected leaf blocks have U's color. Their merged support plus U is
connected. Every other support can be trimmed outside U, since a walk with
both endpoints outside a one-boundary pendant region can avoid that region.
The original partition refines this coarsening and the U payload is unsplit.

Prove this statement on the original live component, then contract U only
as a display. This avoids assuming that original and suppressed edge
identities coincide. Repeat for the concrete bottom-up normalization groups.
After the mixed/unique singleton lemma selects a group, delete its displayed
region from the coarsened partition, keep all original edges/addresses, and
apply the cut induction above. Every external and recursive refinement lift
must be stated explicitly.

## Counts after graph simulation

After those assertions are proved, every output has actual paid cost equal
to pieces minus1 and at least used-colors minus1. At base2, unique-color
detachment decreases the number of colors by1 and charges1; a mixed-cherry
split leaves the number of colors unchanged in each child and has two paid
unit alternatives. The proposed weighted induction then has bound2^(1-r).
For c>=2 the realized-cost lower bound converts it to c^(1-r). Budget pruning
only removes emissions, but its visited prefixes/attempts still contribute
construction work. The existing program count bound addresses those counts;
polynomial per-prefix sizes/operations and reconstruction remain to prove.

These conclusions remain conditional on the original-component, pure-region
coarsening and display simulation proofs above. No source-edge realization,
recursive coverage or mass claim is accepted by this note.
