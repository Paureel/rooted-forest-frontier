# Universal233 source integration

The Boolean source interface and the local graph operations of the exact
source program have Lean proofs. The complete source generator, original
cut-component realization, and full 2.33 algorithm remain OPEN. Fresh
nonauthor review is pending.

`sourcePartition_from_checks` constructs a `CoreGraph.SourcePartition` from
exactly `RMAF.partitionCheck (RMAF.leaves T) bs = true` and
`RMAF.pairwiseEmbeddings T bs = true`. Its supports are the executable minimal
embeddings, indexed by their block positions. Actual vertex validity,
connectedness by one-edge walks, terminal membership and disjointness are
proved. `checkedSourcePartition_owner` proves owner equality exactly when
the original labels occur in a common block. The construction uses no
supplied connectedness or convexity assertion.

`normalize_source_transport` follows the exact `CoreProgram.normalize`
computation. Each homogeneous group contraction first uses the frozen
same-graph coarsening theorem and then constructs the actual quotient source
partition by deleting the two old cherry terminals from walks. A concrete
address map sends every old group to a normalized group containing its full
original-label payload and preserves old block equality.
`checked_normalization_lift` composes this result with the original Boolean
checks and original-label coloring.

`erase_leaf_source_transport` follows the exact executable erase under the
proved distinct-origin state invariant. The proof embeds each path of the
suppressed binary graph into the old graph and constructs new source supports
as hulls of surviving terminals. Original group payloads remain unchanged,
surviving owners retain their equality, and a detached singleton owner has no
surviving terminal. Root suppression is included. The explicit control in
`Controls.lean` shows a suppressed edge expanding to two original edges.

`step_source_progress` composes normalization, the exact chooser and the
actual attempt call. The unique-color branch supplies its graph singleton;
the mixed-cherry branch supplies one of its two graph singletons. A normalized
chooser cannot refuse. The reachable origin invariants exclude an original
root cut, a repeated origin, or erasing the entire current source. Every
nonfinish case therefore has a successful source-preserving continuation
branch with a constructed graph partition and original group lift.

The original edge recorded at that continuation still needs its residual
component theorem. `FIRST-GAP.md` states the exact missing assertion. A proof
that the finite budget reaches an output, complete original refinement
reconstruction, realized cut cost, raw mass and polynomial per-prefix work
also remain necessary. None follows merely from the local continuation fact.

## Retained replay

The receipt `replay/20261015T072236Z` rebuilds 18 exact source modules from
fresh copies, including the original RMAF dependency and every imported
frozen core and geometry module. It audits all 449 explicit declarations,
with only `Classical.choice`, `propext` and `Quot.sound` reported. Nine positive
controls compile. Three false-proposition controls are rejected for the
expected reason: overlapping source embeddings, two old cherry terminals
asserted to have different quotient vertices, and a suppressed edge asserted
to be one original edge. Source hashes match before and after the replay.
The 18 source builds took 11.741541 seconds in this replay.

All proof and replay files are local. No frozen author source, verification
script, integrity pin or earlier result was modified. No X0 census was rerun.
The core and geometry packages were read during proof development; their
results and this author's compiler replay are development evidence. They
cannot substitute for fresh nonauthor proof and consuming-interface review.
