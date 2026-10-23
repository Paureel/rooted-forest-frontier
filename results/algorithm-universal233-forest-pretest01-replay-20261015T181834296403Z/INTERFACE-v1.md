# Pretest consumer interface v1

Import `ForestPretestSemantics` and use namespace `ForestPretest01`.
Arguments are `T : Option RMAF.Tree` and `ss : List RMAF.Tree`.
`Forest` abbreviates `List (List Nat)`.

The executable entry point is `pretest01 T ss : Result` with constructors
`.refused`, `.rejected`, and `.found F`. The return includes the complete
label partition F; the caller can reconstruct source restrictions using
existing original `ForestState` materialization interfaces.

`found_globally_minimum T ss F h` for
`h : pretest01 T ss = .found F` gives:

- `ForestState.agrees T ss F = true`;
- `ForestState.additionalCost ss F ≤ 1`;
- for every G with original `ForestState.agrees T ss G = true`,
  `ForestState.additionalCost ss F ≤ ForestState.additionalCost ss G`.

`rejected_lower_bound T ss h` for a `.rejected` result gives
`ForestState.proper T ss = true` and a cost lower bound of two for every
actual agreement forest G. `refused_iff T ss` equates `.refused` with
malformed input, expressed as `ForestState.proper T ss = false`.
`pretest_complete` maps any actual cost≤1 forest to a found global minimum.

No target-disjointness or ordinary callback/IH premise occurs in these
statements. The proof applies to arbitrary current source components and
original natural-number labels, including internal target overlap.

`universal_coverage` gives a candidate for each actual cost≤1 forest with
the same additional cost and a `ForestPerm` proof. `ForestPerm` is generated
only by `List.Perm` on labels within a block, `List.Perm` on blocks, and
append/transitivity; it has no agreement, minimum or desired-cover field.
`agrees_perm` proves original agreement invariant under that relation.

No parent dispatcher, pool, scheduler, or local IH module was modified.
A caller must account separately for its use and the qualified source work.
