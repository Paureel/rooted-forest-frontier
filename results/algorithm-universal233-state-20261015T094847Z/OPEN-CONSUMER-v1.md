# Common-cherry reduction remains open

The singleton transition is proved in Reverse.lean. Common-cherry separation and endpoint restriction topology are proved in CherryGraph.lean and CherryTopology.lean. This document names the first missing graph statement for assembling the no-larger common-cherry replacement. It is a proposed proof obligation, not an assumption or a proved theorem.

```lean
-- All names below denote the original executable RMAF objects.
∀ (t : RMAF.Tree) (A C : List Nat) (a b : Nat),
  (RMAF.leaves t).Nodup →
  ForestState.cherry a b t = true →
  a ∈ A → b ∉ A → a ∉ C → b ∉ C →
  RMAF.disjointVertices (RMAF.minimalVertices A t)
    (RMAF.minimalVertices C t) = true →
  RMAF.disjointVertices (RMAF.minimalVertices (b :: A) t)
    (RMAF.minimalVertices C t) = true
```

This statement must be applied separately to the actual target and actual source component containing the cherry. Their cherry addresses may differ. The compiled theorem `synchronized_endpoint_reassignment_topology` proves the corresponding `restrictionAgrees` assertion; it does not prove this embedding assertion.

After this assertion, the following common-cherry work still needs proof: explicit no-larger finite forest replacement and source-family bookkeeping; contraction of every replacement block against the actual contracted trees; fresh-label partition validity; expansion of every reduced agreement with exact block count; strict current-label decrease; and decision equivalence for every budget. The executable `contract`, `expand`, `contractBlock`, `expandBlock`, and `cherryReady` definitions and finite controls are present. Their presence does not establish those universal assertions.

All three main solver milestones remain open. Fresh nonauthor acceptance of the completed singleton and partial cherry proofs remains pending. No source-priority, full-algorithm, or runtime conclusion follows from this arm.
