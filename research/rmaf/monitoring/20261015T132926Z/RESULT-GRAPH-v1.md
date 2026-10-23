# Common-split graph minimum: author checkpoint

AUTHOR KERNEL CHECKED; fresh nonauthor acceptance remains OPEN. The complete
algorithm, its correctness and the smaller running-time base all remain OPEN.
This release proves a graph subroutine. It does not implement its recursive
Rule5 caller or establish its source running time.

`DerivedMinimum.common_split_derived_minimum` takes proper original labelled
binary trees T,S, the checked two-block partition [X,Y] in both, and an actual
nonroot subtree address in each tree whose descendant labels are either X or Y.
Thus either side may contain the original root. Its remaining inputs are the
actual ordinary restrictions, actual marked restrictions with one chosen leaf
from the other side renamed to an explicit fresh label, and witnessed minimum
AF costs m,n,mr,ng for those four pairs. A minimum means an actual AF witness
and a lower bound against every literal AF of that pair.

The theorem derives an actual original AF witness and a lower bound against
EVERY original AF at cost

    if mr = m and ng = n then m + n else m + n + 1.

It takes no global minimum, safe-cover, gluing, projection, reconstruction or
desired-cost premise. Marked costs lie between the respective unmarked cost
and that cost plus one. Every equal-sum original AF has a crossing block; its
literal projection gives both marked lower flags at no extra component. In
the stable case, the actual marker-owning blocks have nonempty original parts.
Original cut geometry supplies their merged topology and both complete
original embedding checks, yielding a forest of cost m+n. Otherwise ordinary
concatenation gives cost m+n+1 and equal-sum projection rules out m+n.

`ForestMerge.original_forest_merge_of_checked_embeddings` is only a final
checker assembly helper with explicit merged-embedding premises. The final
theorem discharges those premises in `MergeStable.original_stable_marked_merge`;
it does not treat them as a proved geometric interface merely because they
occur in a helper signature.

The canonical replay is
`results/algorithm-universal233-common-split-graph-20261015T132015611066Z/receipt.json`.
It rebuilds all 151 scientific modules from exact source bytes in an isolated
LEAN_PATH, including 35 modules authored in this scope. It audits all 4,238
stored producer occurrences (4,210 resolved scientific names), actual kinds,
types, bodies, references and axiom references. The only axiom references are
Classical.choice, Quot.sound and propext. Full records are retained as 151
lossless gzip archives with checked raw-byte and compressed hashes.

The original nine positive control groups and five false extensions preceded
universal proof construction. Seven additional positive groups and four false
extensions test the completed graph interface, including a genuine root-side
split with opposite rooted orientations. These later controls are labelled
postconstruction. A first postconstruction fixture incorrectly predicted one
literal child order; its failed source and diagnostic are retained. Correcting
that expected constructor order changed no mathematical theorem.

Before its first candidate application, the revised producer instrument passed
fresh clean-twin, same-name/same-type hostile-axiom in both import orders,
unused-private-axiom, missing/duplicate/unresolved record and changed-source
controls. Its mathematical source had already been authored/contacted. This is
author validation, with declared reuse of completed author instruments; it is
not an independent verification. The runner is frozen after execution; only
the scientific sources and specified detector inputs had pre-execution pins.

The first consuming algorithm gap is printed in FIRST-GAP.md. No complete
solver, executable common-split witness selector, source-cost envelope,
termination theorem or improved exponent follows from this release alone.
