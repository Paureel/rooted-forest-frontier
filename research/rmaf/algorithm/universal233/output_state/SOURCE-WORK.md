# Source work qualification

This is a conservative source-level counting argument for materialization and grouping. It is not a Lean cost-semantics theorem, a compiled-machine runtime result, or a bound for the recursive solver, generator, or full ForestState checker.

Let n be the number of distinct original source labels, N its number of tree nodes, and k the number of checked blocks of Q. A proper ordinary binary source has N=2n−1. The original checked partition gives k≤n and Q.flatten length n. Nat label equality is counted as one operation; a bit-cost account must also charge label comparisons.

The original restriction function visits at most N nodes for each Q block U and uses linear list membership in U at a leaf. Materializing all Q restrictions therefore takes O(N(n+k)) list/tree operations, conservatively O(n²). A coarser O(kn) bound on the number of materialized tree nodes gives O(n²) retained data without needing any tighter structural sharing argument.

The executable group selection is `owned ss U`, a list filter using `contained (leaves s) U`. Recomputing naive append-based leaves of a tree of at most N nodes takes O(N²). Testing containment takes O(n²) in the same coarse bound. Applying the three A/B/C filters to at most k current components therefore takes O(kn²), conservatively O(n³), and returns the whole B list plus the unique singleton A/C lists proved in opposite_grouping. A direct original `restrict A S` or `restrict C S` computes the selected singleton tree within O(n²).

An implementation may bind the materialized source list once and reuse it for the three filters. The conservative combined materialization/selection bound is O(n³) with O(n²) retained data in the stated unit-cost source model. The executable definitions establish the returned values; this note does not establish correspondence between those source operations and compiled Lean allocation, sharing, garbage collection, or machine instructions. The checker and permutation invariance theorems are value-level proofs.
