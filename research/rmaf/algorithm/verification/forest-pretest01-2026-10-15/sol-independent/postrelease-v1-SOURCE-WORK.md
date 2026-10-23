# Independent source-work ruling

This is source-level reasoning from the released definitions, not a proved
machine-instruction bound. The kernel count theorem establishes list-entry
count only. Let n be total current-source leaves on a proper input, r the
number of current components, h maximum original address length, and b the
maximum input-label bit length. Here r <= n and h <= n-1 unless empty.
Malformed inputs require their own target-plus-source input size; the
properness guard executes before candidate generation.

`ForestPretest01.unchanged` maps leaves over every component. `oneCuts`
walks the current forest, maps every original nonroot source address to
subtreeLabels/complement and appends unchanged remaining components; its
recursive tail candidates receive the retained head block. No edge-partition
deduplication occurs. `Pretest.vertices/edges` materialize original Bool-list
addresses, whose length is not constant. `subtreeLabels` follows the original
address and traverses the subtree; `complement` filters all component labels
using membership in subtreeLabels. Its displayed source does not cache that
subtree list outside the filter, so a conservative source accounting must
allow repeated traversal. Repeated unchanged blocks and list appends also
cost work even when a candidate later fails.

`pretest01` first checks target Nodup and the literal current-source
partition. On proper inputs `best` recursively tests every generated
candidate with the entire original `agrees`; it is not a first-success
shortcut. The complete `agrees` checks target partition, every block's
source owner, original target embedding hulls, and each source's filtered
family partition, restricted topology and original source hulls. Internal
target overlap is consequently charged and checked. No per-component
target-clearance premise makes this work disappear. Failed candidates can
consume the same whole-candidate checks until their short-circuit failure;
an upper bound must charge all of them.

`partitionCheck` flattens blocks and counts each target label, then checks
every returned label. `contained/family` use nested label-list membership.
`restrict` traverses both tree children with selected-label membership and
suppresses unary nodes. `sameShape` may try both sibling alignments; its
recursive node-pairs lie in the product of the two restricted-tree node
sets, yielding a polynomial structural bound, rather than assuming one
alignment always succeeds. `minimalVertices` and `rootedSpan` retain all
original path vertices and can repeat span traversals above the LCA.
`pairwiseEmbeddings` repeats those hull constructions for block pairs;
`disjointVertices` scans lists of Bool-list addresses. Both hull-list size
and address equality length enter the accounting.

These explicit finite nested traversals admit a conservative polynomial
source-operation accounting on proper finite binary inputs. Even a blunt
accounting can charge O(n^3(1+b)) per hull construction, O(n^2) block-pair
tests per component, up to n source components and O(n) candidate entries;
this gives an intentionally loose O(n^7(1+b)) envelope under a stated list
operation/bit-comparison model. It is reviewer reasoning, not an optimized
bound or a compiled Lean runtime theorem. Source sharing, tail-recursion
rewrites, allocation, garbage collection, builtin Nat implementations and
code generation have not been proved in that model here. In particular,
arbitrary Nat labels cannot be charged as fixed-width indices.

The exact generated count is 1 + sum source-edge counts. With n_i leaves
per component, edges_i + 2 = 2 n_i, hence count + 2r = 1+2n (including
empty input, count one). Repeated partitions remain counted. This permits
neither an O(n) instruction claim nor a free returned payload: each proper
candidate contains n label occurrences, and found returns the complete
partition. Current-source edge addresses identify local current-tree edges;
the return does not include a globally recovered original source-cut union.
Materialization/recovery, address transport and their costs remain separate
caller obligations. No per-node recovery cost is obtained by this review.

The proof-only source-core generation used to establish a separation edge
does not enter the displayed executable pretest. Its broader algorithmic
work bounds are not imported as runtime facts. Parent LocalIH/current-budget
binding, main dispatcher integration, compiled IR/runtime correctness, and
all global algorithm/base/novelty milestones remain OPEN.
