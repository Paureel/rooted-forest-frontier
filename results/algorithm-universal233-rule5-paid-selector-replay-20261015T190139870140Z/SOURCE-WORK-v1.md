# Paid selector source work v1

`rows_linear_bound` proves at most sixteen candidate bottom rows per actual
original source vertex: eight sibling patterns and two endpoint orders.
Each row comes from an actual source subtree lookup and a literal bottom
parser. It contains no desired-cover, paid-guard or minimum field.

The builder finds target leaf addresses over original target vertices,
looks up the actual selected core subtree, and checks finite original
geometry: proper labels, exact source bottom, finite actual cherry,
original pendant count, core labels, original terminal leaves, exact
frontier and its incoming/outgoing hull membership. Every check is a
finite tree/list computation. All actual source and target vertices are
unsuppressed original Boolean addresses; the selected d/u/v are retained.
`buildSelected_complete` proves nonrefusal from the actual final selector's
sound second output, using its derived SourceGeometry only in the proof.

Count tree/list constructors, finite branches and bounded-word operations
as source primitives. For N input tree/list cells, original addresses have
length at most N and there are O(N) candidate rows. Tree lookup, list
membership, restriction, minimal span, incident frontier and shape tests
have polynomial source work in N. Repeated checks and target vertex scans
remain polynomial. The Lean work proof certifies row count; it does not
formalize a complete instruction count for every inherited primitive.

Let B be one plus the maximum bit length of an original natural-number
label. Bounded-word labels permit unit-cost comparisons; arbitrary Nat
labels require their actual bit costs, polynomial in B. Original vertex
addresses also carry their full bit/list cost. The selected geometry keeps
original target/source subtrees and original labels. Request outputs keep
the complete current source forest, full original cut list and full
original-label partition; their payload and construction costs are paid in
the source model. No compact encoding or constant-cost arbitrary Nat is
assumed.

`requestFor` subtracts every member of the original cut list exactly once
before issuing a child request and retains branch order and multiplicity.
`full_state_cost` identifies the materialized forest additional cost with
F.length minus the actual current partition length. Final original-cut
recovery remains a separate one-time operation in the parent algorithm.
There is no runtime ghost, minimum oracle, recursive solver, compiled
machine-time theorem or complete parent source-bill theorem in this package.
