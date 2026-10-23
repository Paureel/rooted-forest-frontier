# Merge adversary result

NO-FIRE-BOUNDED: the exact check found no counterexample among 192 valid
child-family pairs on the declared shapes. The universal merge statement
remains open pending its construction and fresh semantic, control, interface
and axiom review. No old result count contributes to this result.

## Executed controls

The inherited suite passed all 5 positive fixtures, rejected all 4 malformed
merge inputs, rejected all 4 wrong numeric propositions while accepting all
4 clean twins, and rejected all 3 corrupted supports while accepting all 3
clean twins. The separate prefix/owner method reproduced every inherited
expected field. These counts refer to distinct controls; their repeated
execution before the pilot and main search adds no new controls.

The four numeric diagnostics, expressed as claimed minus actual, were:

| Control | Claim | Actual | Residual |
| --- | ---: | ---: | ---: |
| Charge merged open T1 | 1 | 0 | 1 |
| Retain two T1 open indices | 2 | 1 | 1 |
| Coalesce other indices by color | 1 | 3 | -2 |
| Charge closed indices twice | 6 | 3 | 3 |

The checker mutation audit disabled numeric-claim detection in a separate
copy. That copy missed all four wrong numeric claims, and the control driver
returned `CONTROL-FAILURE` with exit code 1. All four clean twins still
passed. The unmodified checker passed the same controls; the mutated copy
was never used for enumeration.

Supplemental controls rejected duplicate indexing, incomplete indexing,
an out-of-tree vertex and an unmarked root owner. A repeated-label case
with collision-prone textual names passed. Two outputs remained valid
geometric families but violated exact retention: one added an unused
internal vertex to the merged region, and one renamed a surviving index.
The transition checker rejected both while accepting their clean twins.

## Search denominator

The generator enumerated canonical set partitions of vertices with an
optional unowned internal-vertex class. The root had a live owner and every
leaf had an owner before validation. Both checker methods then decided all
family obligations independently; they agreed on all 140 candidate inputs.
The valid-family counts were:

| Child shape | Vertices | Candidate partitions | Valid live families |
| --- | ---: | ---: | ---: |
| Leaf | 1 | 1 | 1 |
| Two-leaf cherry | 3 | 5 | 3 |
| Left three-leaf comb | 5 | 67 | 11 |
| Right three-leaf comb | 5 | 67 | 11 |

All 12 ordered shape pairs with total leaf count at most five were checked,
for 192 family pairs. The main output passed the fresh graph family check,
exact per-index support and leaf-node preservation, retained-index equality,
merged leaf union, count sum−1 and closed-cost sum in every pair. The
prefix/owner route also checked output convexity and reconstructed the
expected supports, indices, counts and costs. All enumerated leaf labels
were `x`, so repeated label values did not collapse indices or leaf vertices.
Index names in this enumeration are canonical representatives up to
renaming; the supplemental fixture checks a noncanonical name choice.

A pilot sampled at most 16 pairs from each ordered shape pair and checked
124 pairs. The post-warm-up maximum observed per-pair time was
0.00017941700025403406 seconds. Before main execution, the saved launch
calculation projected 0.06336435604680446 seconds for all 192 pairs, including
enumeration and an additional complete pilot-time allowance. The complete
main driver, including control replay and candidate enumeration, measured
0.03618937499959429 seconds. These are process-internal wall times; command
startup and tool transport are outside that measurement. Pilot pairs overlap
the main run and are not added to the 192 denominator.

## Semantic hazards

1. `CostRoute.Family` indexes distinct leaf-bearing supports. Equal colors
   or equal labels do not identify indices. `FamilyAssembly.lean:5` explicitly
   permits repeated labels, and its structure at lines 65–74 has no distinct
   label hypothesis. The distinct-label wrapper at `FamilyModel.lean:35–37`
   is a separate object and cannot be silently imposed on this target.
2. Coverage is required only for leaves (`FamilyAssembly.lean:72`). Filling
   every internal vertex changes the exact support claim even when it
   preserves family validity. Both the inherited unused-vertex fixture and
   supplemental added-vertex corruption exercise this distinction.
3. Convexity uses every vertex of the LCA-to-endpoint paths
   (`ConnectedRegions.lean:7–11`). LCA closure alone is insufficient; the
   removed-stem corruption fails the executed graph and prefix checks.
4. A boundary must own the child root and a leaf (`FamilyAssembly.lean:70,74`).
   Removing either hypothesis changes the regime; the corresponding frozen
   malformed controls are input rejections, not theorem counterexamples.
5. Cost subtracts the open boundary charge from the block count
   (`FamilyAssembly.lean:58–79`). The merged open index is not charged.
   The T1 controls distinguish zero closed cost from one.
6. Geometric family validity does not imply exact index/support transport.
   Those equations require their own assertions and proof fields. This arm
   supplies no child-restriction or four-transition correspondence claim.

## Provenance and limits

`SPEC.md`, both checker routes, the control driver and supplemental controls
were hashed in `PREEXECUTION-SHA256.txt` before either checker ran. The route
specification and checker implementations preceded the audit of the Lean
definitions. Existing author checkers, old receipts and new merge proof code
were not read or imported. All new evidence is under this adversary directory
or `results/triple-family-transitions-adversary-*`.

Route G builds explicit undirected adjacency lists and uses BFS paths. Route
P scans vertex owners and uses common-prefix paths; it imports no Route G
code. Both routes share this author, the specification, fixtures, binary
address convention and Python standard library. Their agreement supplies an
algorithmic cross-check. Fresh-author verification remains the parent's
separate obligation, and the graph-to-Lean semantic correspondence has not
been formally proved here. Neither larger trees nor color/mask admissibility
were tested. No toolkit-wide suite or Lean compilation was run by this arm;
no toolkit source or Lean source was changed.

## Replay

Run from the workspace root with the project interpreter:

```sh
./bootloops-python research/rmaf/triple_dp/family/transitions/adversary/run_adversary.py --mode controls --output results/triple-family-transitions-adversary-replay-controls.json
./bootloops-python research/rmaf/triple_dp/family/transitions/adversary/run_adversary.py --mode bounded --gate results/triple-family-transitions-adversary-launch-gate.json --output results/triple-family-transitions-adversary-replay-bounded.json
```

The retained plant receipts contain the exact mutation command and source
hashes. The bounded receipt contains every tree-pair denominator, measured
case time and checker/specification hash. The main evidence files are
`results/triple-family-transitions-adversary-controls.json`,
`results/triple-family-transitions-adversary-checker-plant.json`,
`results/triple-family-transitions-adversary-pilot.json`,
`results/triple-family-transitions-adversary-launch-gate.json`, and
`results/triple-family-transitions-adversary-bounded.json`.
