# Literal grouped ForestState interface

All theorem names below are in namespace ForestGroups. All source labels are
Nat and all forests are literal lists of label lists. The actual original
checker is ForestState.agrees, retrieved from frozen state_reductions/State.lean
lines 6-29. The definition includes proper labels/source partition, target
partition, whole-current-source containment for every block, actual target
minimal embeddings, and each source tree's partition/topology/embedding check.

| Result | Inputs that must be established | Conclusion |
| --- | --- | --- |
| GroupDefs.local_proper | proper original state, checked Q label partition, each current source tree wholly owned by a group, U in Q | local restricted target and literal owned source list are proper |
| GroupForwardProof.forward_decomposition | original agrees, checked Q, source ownership | every family U F agrees locally |
| GroupReverseProof.reverse_reconstruction | original proper, checked Q, ownership, CrossClear on current source trees in different groups, every local agrees | Q.flatMap G agrees on original target/current source forest |
| GroupCostProof.forward_exact_cost | original agrees, checked Q, ownership | sum local additionalCost = original additionalCost |
| GroupCostProof.reverse_exact_cost | original proper, checked Q, ownership, local agrees | sum supplied local costs = concatenated original cost; cross-clear is unnecessary for this arithmetic equality |
| GroupCostProof.forward_every_budget / reverse_every_budget | corresponding reconstruction hypotheses, arbitrary q | exact equivalence of summed and original budget |
| GroupPriority.retained_A_one_plus_Bforest | literal [a]++bs++cs, checked A/B/C partition, source ownership, piecewise cross-clear, actual A agreement cost1, arbitrary Bforest agreement, completed C agreement cost0 | concatenated agrees and exact cost1+costB |
| GroupPriority.retained_A_one_Bforest_no_C | literal [a]++bs, checked A/B partition, ownership, A clears each Bpiece, actual cost1 A and arbitrary Bforest agreement | empty completed-C case |
| GroupPriority.residual_query_lift | preceding three-group inputs and positive q, successful solver query at q-1, child-specific ResidualSolverContract | original concatenation agrees within q |
| GroupPriority.residual_query_complete | child-specific contract, proper child state, actual child forest within budget | solver returns some valid child forest within budget |

CrossClear is defined in GroupDefs.lean lines 14-17. The quoted source text is
`∀ s ∈ owned ss U, ∀ r ∈ owned ss V,` followed by
`Clear (minimalVertices (leaves s) t) (minimalVertices (leaves r) t)`.
Only U ≠ V is compared. The construction of the local lists is part of the
program, and its validity is proved from original partition/source ownership.

The restriction transport lemmas are retrieved development inputs from frozen
restriction_bridge/Restriction.lean and Embedding.lean. Their import names are
adapted in STACK-PINS.json without altering theorem bodies. Minimal embedding
monotonicity is retrieved from frozen geometry/Composition.lean. The new proof
reconstructs group partition uniqueness, source-family filtering, cross-group
block clearance, and natural subtraction balance. These retrieved inputs are
not claimed as independently rederived here. The dependency source bytes are
checked against completed frozen manifests during isolated replay.

Consumer limit: ResidualSolverContract is local to the exact child target,
whole current bs list, and query budget. It asserts both failure completeness
and returned-witness soundness. It is assumed in residual_query_lift, never
inferred from a positive minimum or from a statement about the free whole B
parent tree. Termination, original full cut-edge reconstruction, and global
branch coverage need separate proofs. No source-cut union occurs in this API.
