# Actual output source states

Author kernel result; fresh nonauthor verification is pending. All three main algorithm milestones remain OPEN. The reconstructed object is a labelled agreement forest. Original-source cut-address reconstruction and a complete recursive solver require separate theorems.

`OutputState.sourceForest S Q` is executable `Q.filterMap (fun U => RMAF.restrict U S)` (OutputDefs.lean:9). Every current source component is an ordinary original restriction. `checked_materialization` (Materialize.lean:35) proves no checked block is missing, the exact component labels up to list permutation, proper labels and nonempty leaves, and the exact number of components. `sourceForest_proper` (Materialize.lean:64) proves the actual finite ForestState is proper; `exact_additional_cost` (Materialize.lean:72) gives `F.length-Q.length`.

The main equivalence is `agrees_iff_original` (Equivalence.lean:112): for proper equal-label original T,S, an original checked Q, and **source** `pairwiseEmbeddings S Q=true`,

```
ForestState.agrees (some T) (sourceForest S Q) F = true
  ↔ RMAF.agreement T S F = true ∧ RestrictionBridge.Refines F Q.
```

The hypothesis list contains no target-Q embedding premise. Original target embeddings are checked on F inside `ForestState.agrees` (retrieved definition: state_reductions/State.lean:26). `source_topology`, `source_forward`, `source_reverse_local` and `source_reverse_global` (Equivalence.lean:5,10,55,67) use the literal original restriction identities and the original source embedding checker in both directions. Cross-source blocks use the original source-Q embeddings; same-source blocks use transported local checks. No ordinary target partition reconstruction theorem requiring target-Q embeddings is used.

`generated_source_bridge` (OppositeGroups.lean:7) consumes actual original `generate` membership and invokes the completed `Assembly.generated_source_valid` (assembly/SourceValidity.lean:87). Source validity is a derived result. Its conclusion includes properness, literal equivalence, materialized length and exact cost for every F.

`opposite_grouping` (OppositeGroups.lean:83) accepts an actual `sideOutputs` member and the completed `BinaryCheap.OppositeSafe`. It proves unique retained A/C ownership as literal singleton lists, source restriction equations, all B pieces as the executable `ForestGroups.owned (sourceForest S o.partition) B`, properness, a permutation from actual output order to `[a]++bs++[c]`, and piecewise `PriorityClear`. No pair of B pieces is required to be target-disjoint. The owned A/C lists select the unique retained components; their literal source trees also equal `restrict A S` and `restrict C S`.

`source_permutation` and `cost_permutation` (Permutation.lean:12,24) prove the actual checker and cost invariance. `owned_three_permutation` (Permutation.lean:27) proves the regrouping from source ownership and checked parent labels. The concrete actual output in ActualConsumers.lean:8 has order B1,B2,A,C, so the development consumer does exercise a noncanonical order.

`opposite_local_certificates` (LocalCertificates.lean:48) converts the actual retained original local source-cut certificate into the literal local A ForestState agreement with additional cost one. It converts original C agreement into the literal C ForestState agreement `[C]` with additional cost zero. The local cut certificate's graph realization supplies its actual partition cardinality.

`every_opposite_residual_query` (ResidualConsumer.lean:10) calls the completed `ForestGroups.retained_A_one_plus_Bforest` and `ForestGroups.residual_query_lift` (forest_groups/GroupPriority.lean:81,144). The supplied solver contract is for the exact restricted target and the **whole current B source list** at q−1. The theorem returns the actual original-order ForestState agreement, original labelled agreement and output refinement, exact additional cost `1+costB`, and the requested budget. The required positive q and child-specific `ResidualSolverContract` remain explicit hypotheses.

Completed state, restriction, source-core/assembly, grouped and binary-cheap files are retrieved development inputs. STACK-PINS.json and BINARY-STACK-PINS.json record original and adapted hashes. Import aliases identify identical restriction proof bodies: DepthRestriction→GroupRestriction, Embedding→GroupEmbedding, Partition→GroupPartition. Proof bodies remain unchanged. No unfinished final-cut, main-both-bad, or reviewer source was consulted.
