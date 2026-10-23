# Source work — qualified inspection bound

The Python development selector preserves actual sibling order, original
addresses, labels and cut partitions. It repeats every earlier-priority and
Rule4 pretest in both orientations. It charges literal original cut addresses,
checks distinct/nonempty cuts and rejects leafless or redundant cut regions.
Every materialized partition has paid+1 nonempty components. Type3(ii)'s
multiple original arcs are all retained and paid; the worst branch vector is
not substituted for its actual cost. A target-side branch records its role.

For n original labels there are O(n) original vertices and cherries. With the
current unoptimized Python address strings, span construction is bounded by
O(n^3) work including copied prefixes; one original pendant computation has
the same bound. Checking all actual cherries costs O(n^4). Repeating those
global pretests for every candidate in both orientations gives a conservative
O(n^5) selector inspection bound. This counts rejections, pretests and copies.
The bounded branch lists contain at most five children, except a type3(ii)
cut list itself may contain O(n) original addresses. Materializing/copying
all their literal cut partitions and restricted source data fits O(n^3)
additional work and O(n^2) address/output space at one local call.

These are inspection bounds for development code, not extracted Lean
operation-count theorems. This package does not provide a complete recursive
solver, a uniform selected-case cover, or a full source-work recurrence.
Exact child-specific bounded solvers and minimum choice are still consumers.
The completed CherryBranching remaining-budget/ExactBoundedChild interface
can be reused once that cover and actual paid-child binding are proved;
its mere import is not local completion. Final original cut recovery must
use the completed recovery call once on the selected final AF, with its own
separate source-work qualification, rather than unioning display-edge lists.

The finite AF checks on 6–8 labels use the completed ordinary partition
oracle. They are bounded development diagnostics, not the claimed faster
solver or a uniform proof. Larger wrapper fixtures were not enumerated.
