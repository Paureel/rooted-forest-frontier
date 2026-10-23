# Literal all-good case interface

`AllGoodDP.run T ss` accepts exactly its executable `allGood` guard. Inputs
are an `Option RMAF.Tree` and an ordinary literal `List RMAF.Tree`. Its guard
checks `ForestState.proper T ss` and full-component target agreement for
every listed source. Labels are arbitrary natural numbers. No hypothesis
asserts disjoint target embeddings of current source components.

`ExactMinimum.run_total_exact` returns a literal labelled forest F with:

* `run T ss = some F`;
* `ForestState.agrees T ss F = true`;
* `additionalCost ss F + ss.length = F.length`;
* `additionalCost ss F ≤ additionalCost ss G` for every literal checked
  agreement G, with no restriction to algorithm-generated forests.

`ExactMinimum.decideBudget_correct` handles every natural budget q. The
answer is true exactly when some literal checked agreement has additional
cost at most q. `none`/empty is included; a nonempty proper target forces a
nonempty source list. The bad-topology control fails the guard.

The proof derives unique owner colors from the source-label partition.
`StateSoundness` proves the original source partition, restricted topology,
and minimal-embedding checks using literal restriction and labelled rooted
isomorphism transport. `TargetEmbedding` proves actual unsuppressed target
minimal-embedding disjointness by induction on reconstructed components.

`LowerBound.agreement_coloring` uses completed final-cut recovery on the
target and converts its actual connected components into an admissible
owner coloring with at most |G|-1 changes. This certificate is a proof
witness; the executable all-good case does not run recovery. Combined with
the minimum-coloring DP and the reconstructed block-count bound, this proves
minimum over all checked agreements. `sources_le_blocks` separately proves
the source-count offset is exact, and `candidate_no_leafless` proves no
empty monochromatic component remains in a minimum coloring.

The later grouped-state caller must prove its own literal all-good guard
before using this case. This package does not assume an outside-clear group
premise and does not prove a complete main solver, its selection/termination,
or its global recurrence. All three main milestones remain OPEN. It makes
no novelty claim. The polynomial bound is qualified in COST-MODEL.md.
