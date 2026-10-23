# First unproved consumer

The literal grouped ForestState forward/reverse reconstruction, exact cost,
retained A cost-one plus arbitrary residual Bforest, and conditional q-1 query
lemmas are authored in this directory. Independent nonauthor mathematical
reconstruction, adversarial checking, and interface ruling remain pending.

The first algorithmic consumer is an implementation and well-founded recursive
proof establishing `ResidualSolverContract solve (localTarget T B) bs (q-1)`
for the whole current B forest. The contract is an input to
`GroupPriority.residual_query_lift`; this author package does not establish it.
The original current source list, its labels, and any externally accumulated
paid cuts must remain accounted for by that consumer.

Final reconstruction of all original source cut edges is separate. The present
proof validates the literal finite source/target embedding model and adds
block-count differences. It supplies no same-parent union of source cuts, no
full reduction normalization, no global recursive coverage theorem, and no
O(2.33^k) analysis. All three main milestones remain OPEN.
