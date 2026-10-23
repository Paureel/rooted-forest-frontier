# Route amendment v2, 2026-10-14

The immutable v1 route pin remains unchanged. No in-regime control failed and
no claim was weakened. During proof construction, the selected-clade detour was
replaced with an exact recursive support summary. This is a derived organizing
choice, not retrieved from another route: no graph-route, parent LocalSplit,
or other transport implementation was read.

The five fields record emptiness of A and C rooted spans, disjointness of A's
rooted span and C's minimum support, the reversed mixed test, and disjointness
of the two minimum supports. `supportProfile_node` proves the node composition
formula from the actual executable support lists. `supportProfile_restrict`
then proves invariance under the actual selection and suppression recursion,
and `supportProfile_rootedIso` proves invariance under child swaps.

The resulting exact equality needs only A⊆B, C⊆B and restrictionAgrees t u B=true.
The stronger generality is a compiled consequence, not a replacement assumption:
the original uniquely-labelled, complementary, nonempty block use case supplies
these subset hypotheses directly. Disjointness is not assumed by the equality
lemma; the directed corollary assumes only the original tree's disjointness.

General proofs are author-compiled, awaiting a nonauthor fresh review and the
parent's consumer trace. They do not close G3/G4, the one-tree split or the
agreement-partition replacement by themselves.
