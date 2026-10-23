# Missing formal transport

The graph theorem `DegreeTwoGraph.actual_degree_propagation` proves a statement
about one actual tree. The formal refinement theorem still needs the following
transport statement, together with existence of the source deletion split.

Let t,u be actual uniquely labelled RMAF trees. Let B be a nonempty duplicate-free
list contained in the leaf labels of each tree, with `restrictionAgrees t u B =
true`. Let A,C be nonempty duplicate-free disjoint lists whose union is B. Assume
`disjointVertices (minimalVertices A t) (minimalVertices C t) = true`.

Required conclusion:

1. `restrictionAgrees t u A = true` and `restrictionAgrees t u C = true`.
2. `disjointVertices (minimalVertices A u) (minimalVertices C u) = true`.

No address equality between t and u is a hypothesis or conclusion. Equal full
label sets outside B are unnecessary. The four nesting inclusions in the local
target follow separately from `actual_support_mono` and the label inclusions.

The source hypothesis is essential: merely partitioning the labels of an
agreement piece does not ensure that its two t embeddings are disjoint. The
ordinary graph route obtains that hypothesis from the degree-two deletion.

The additional formal graph existence statement is: deleting v of exact degree
two from the actual minimal support produces exactly two nonempty connected
components, each containing selected occurrences; their occurrence labels give
A,C with both actual t hulls inside the respective components. The proof is in
ROUTE.md under G-del, but no universal Lean theorem for that construction is
claimed here.

Even after these two statements, a general list replacement theorem must verify
every conjunct of the unchanged `RMAF.agreement` predicate. Only the frozen finite
consumer has been checked in Lean in this arm. The ordinary replacement argument
appears in ROUTE.md under G-consumer. This report does not instantiate `clearRest`
or close G3/G4.
