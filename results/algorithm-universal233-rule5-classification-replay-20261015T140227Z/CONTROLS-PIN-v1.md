# Classification preproof controls

Pinned before new proof code. Reuse of frozen v1 graphs/evaluators is declared
DEVELOPMENT. Original v1 sources and every frozen result remain untouched.

Positive original fixtures: v1 large, two, and outside. For their good block
X and its actual source cherry p,q, target cuts(p,q) have exactly two original
arcs and their descendant label sets equal the other two literal source parts
in one of the two orders. The residual core labels equal X. All actual global
both-orientation guards and parent embedding checks must still pass.

Original root-side positive: T=(((p,y),(q,z)),w), X={p,q,w}, Y={y}, Z={z}.
Exactly y,z are outgoing pq pendants, and w stays in the core. No root incoming
edge is inserted. Both complete sibling mirrors must give the same labels.

Deliberate negative controls:

1. Missing homeomorphism/pruned cherry: T=(p,(y,(q,z))), X={p,q,y}, Y={z}.
   The actual pq pendant list contains y from X. A false exclusion must fail.
2. Missing outside clearance: T=(((p,y),(q,z)),w), X={p,q}, Y={y,z}, Z={w}.
   Y crosses both original pq pendants; the actual hull of Y overlaps X.
   False attachment equality must fail.
3. Missing no-t1 priority: source good X=((p,q),(r,s)), target
   T=((p,(q,y)),(r,(s,z))), source S=(X,(y,z)). Literal X,Y={y},Z={z} are
   disjoint and X is good with two cherries; p,q and r,s each have only one
   target outgoing pendant. False uniqueness without priority must fail.
4. Unpaid/upward cut: the root-side positive must have two original nonroot
   cuts, not three and not an incoming root edge. A corrupted count is caught.

The same comparator is challenged by flipping one expected positive attachment
answer; it must reject and its clean twin must pass. Controls check actual
tree labels/spans/arcs, not synthetic colors or abstract desired geometry.
