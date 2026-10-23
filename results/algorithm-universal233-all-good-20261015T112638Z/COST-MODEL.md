# Polynomial source-operation bound

The all-good case executes `run`, whose guard is the literal `proper` check
and the full-component restricted-topology checks. The accepted branch calls
`candidate`, `solve`, `table`, and `choose`, then extracts leaf blocks with
`split` and a nonempty filter. The call graph contains no set-partition,
vertex-assignment, cut-set, `generate`, or final-cut-recovery search.
`LowerBound` imports final-cut recovery only for its mathematical converse
certificate. Classical choice occurs only in that proof.

Let n be the target vertex count, r the number of current source trees, m the
sum of their vertex counts, and b the sum of the bit lengths of all input
natural labels, plus the input budget's bit length for a budget query. Take
S = n + m + r + b + 1. List constructors, Boolean branches, and word-sized
pointer operations cost one unit; natural-number comparison and arithmetic
are conservatively charged S units each. This dominates label comparison,
counts, DP scores, and comparisons with the input budget. The returned
forest contains original labels, so copying a label is also covered by this
charge. This is a source-operation model, not formal compiled-machine
semantics or a wall-clock guarantee.

`table` recursively evaluates its left and right tables once in `let`
bindings. A leaf has one candidate. An internal vertex has exactly r
candidates, one for each root color in `List.range r`. Each candidate scans
the two child tables using `RMAF.best`; it retains one actual painted child
per side. A scan of k entries performs at most k comparisons and at most
2k score evaluations. Each score traverses at most n painted vertices and
uses at most 6n arithmetic/Boolean primitive operations. Summing over all
vertices gives at most 24 n²(r+1)² score primitives, plus at most
20 n(r+1)² table/list primitives. Final root selection costs at most
12 n(r+1) score primitives. No r^n collection is built or visited.

`ColorDP.table_length` proves the exact row counts.
`ColorDP.visits_bound` proves the coarse table-visit recurrence

    visits r t ≤ vertices t * (r * (2 * (r+1) + 1) + 1).

This recurrence charges one leaf visit and, for each internal root color,
the two finite table lengths and its constructor. The extra score-traversal
factor above is necessary because scores are recomputed from stored paints.
The formal recurrence alone is not a machine runtime theorem.

The owner scan at a leaf checks at most all m source vertices. Across all
target leaves this uses at most 4n(m+r+1) list/label operations. `split`
visits every painted vertex once; its list appends cost at most 8(n+1)²
element operations. It retains empty raw components until filtering, so
every list has at most n components and n labels. No repeated optimization
is hidden in reconstruction.

The input checks are polynomial as written. `partitionCheck` performs
literal count and membership scans over at most n+m+r input entries.
`restrict` visits each tree vertex once and scans the selected label list.
`sameShape` can examine all four child pairings, but every recursive call
visits a distinct pair of original subtree roots: the two roots descend
together, and their address pair uniquely determines the call. Thus at most
the product of the two tree vertex counts is visited; there is no repeated
call at the same pair. Across the source list these operations fit within
50(S+1)^4 unweighted primitives, including the guard's unsuccessful cases.

The displayed contributions, multiplied by the S charge for natural-number
operations and including guard, output, and budget comparison, are bounded
by the explicit conservative polynomial

    1000 * (S+1)^6.

The source inspection relating these helper calls to primitive counts is a
mathematical audit. The kernel separately checks structural termination,
the finite row-size identity, and the coarse visit bound. It does not check
an operational semantics for Lean, allocation, garbage collection, compiler
optimizations, or this final helper-to-primitive correspondence. A fresh
nonauthor source-cost review remains required before acceptance.
