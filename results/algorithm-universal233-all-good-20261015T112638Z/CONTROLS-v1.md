# Pre-proof controls

The JSON pin fixes the fixtures and expected values before DP proof work.
The six-label control has owner colors A,B,C,A,B,C down the caterpillar.
Every two unsplit owner pairs have intersecting target minimal embeddings,
so at most one pair survives. Keeping {2,5} and four singleton blocks attains
the minimum five blocks, hence additional cost two. The crossed quartet
needs three blocks, hence additional cost one. These are manual arguments;
small set-partition enumeration is a separate development check.

The leafless-region false control uses the rooted colored tree with root B,
its two internal children B, and all four leaves A. The B region has three
vertices and four boundary edges. Dropping that region from the list of
leaf-bearing blocks leaves one A block per disconnected A region; its paid
edges must still be included in the coloring count. A proposed equality
between the number of nonempty components and edge changes plus one fails
on this nonminimum coloring. The algorithm may drop empty components only
with a proved inequality and exact leaf coverage.

An independent small enumerator will enumerate set partitions of the target
labels, then run literal topology and original-address minimal-embedding
checks. It is never a production algorithm subroutine. The Lean fixtures
will separately execute the actual unmodified ForestState checker.
