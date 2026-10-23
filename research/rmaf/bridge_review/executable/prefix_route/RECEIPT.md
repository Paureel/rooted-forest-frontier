# Independent prefix-route receipt

The selected-occurrence prefix construction reproduces all nine exact
controls. Lean checked 816 additional executable membership comparisons,
four corruption rejections, and a general theorem that prefix hulls are
connected using `BridgeReview.Adj` and `BridgeReview.Walk`. The structural
argument identifying `RMAF.minimalVertices` with that prefix hull is given
in `DERIVATION.md`; this arm has not formalized that general equality in Lean.

The mathematical argument has no identified missing case. Its formal gap is
the unformalized pair of extraction equalities: `rootedSpan = root prefixes`
and `minimalVertices = prefixes from the selected occurrence LCA`. The
finite checks do not replace those general equalities. This is an
independent proof-and-check arm, without a claim that the full executable
target has been kernel checked by this arm. Full G1, leastness, unique-label
interpretation, restriction transport, complexity, and novelty remain outside
its conclusions.

## Controls and results

`CONTROLS.md` was written after reading the target and before inspecting
executable source or candidate proofs. It freezes the target's five cases,
four additional cases, and four deliberately wrong supports. False means
left, true means right; the table uses 0 and 1 for those bits. No expectation
changed, and no source/spec disagreement was found.

| Case | Exact support |
|---|---|
| ((0,1),(2,3)), {0,2} | {epsilon,0,00,1,10} |
| same tree, {1} | {01} |
| same tree, {0,1} | {0,00,01} |
| same tree, empty selection | {} |
| same tree, {9} | {} |
| ((7,1),(2,7)), {7} | {epsilon,0,00,1,11} |
| duplicate tree, {1,9} | {01} |
| (8,(8,(8,((0,1),(2,3))))), {0,1} | {1110,11100,11101} |
| same long-path tree, {0,2} | {111,1110,11100,1111,11110} |

The prefix evaluator rejected 4/4 corrupted supports. Removing 0 from the
first support also failed the independent graph-reachability check. Giving
the absent label support {epsilon}, choosing only one repeated-label
occurrence, and retaining vertices above the selected LCA all remained
connected, but failed exact membership. These controls demonstrate why
connectedness alone cannot certify the output's membership.

`Finite4.lean` contains 816 sweep theorems, 9 exact-control theorems and 4
corruption-rejection theorems, all proved with `decide`. The sweep comprises
every ordered full binary tree with 1–4 leaves, every assignment of labels
0 or 1, and all eight subsets of {0,1,9}. There are 102 trees and 816
tree/selection pairs. The 176-case pilot is included in that sweep and is
not counted as additional coverage. The positive and negative controls were
executed before the sweep generation.

The intentionally false assertions in `NegativeControls.lean` failed to
compile with both expected errors. Their diagnostics, retained verbatim in
`negative-build.log`, name the false missing-path and absent-label
expectations. The corresponding correct rejections in `Finite4.lean` compile.

## Mathematical route

The fresh evaluator traverses the tree to collect selected leaf *occurrence*
addresses. It computes their longest common prefix and then takes all
prefixes between that common prefix and each selected occurrence. A second
traversal constructs parent/child graph edges and checks reachability in the
proposed support. Neither calculation calls a recursive span implementation.

The written structural proof first identifies `rootedSpan` with all prefixes
of selected leaf occurrences. Its empty test therefore detects an empty
occurrence set. At a node, if exactly one child contributes, the common
prefix and minimal support both acquire that child's initial bit; if both
contribute, their common prefix is empty and the minimal support is the
root together with the two rooted child spans. A selected leaf occurrence
therefore supplies a member and proves nonemptiness. Repeated labels select
all matching occurrences, and an absent label supplies none.

Every member q in a prefix hull has a terminal p with c <= q <= p, where c
is the selected occurrence LCA. Appending successive bits from c to q
constructs a walk entirely within that hull. Reversing one such walk and
concatenating another connects any member pair. The Lean theorem proves
this construction with the exact imported graph constructors.

## Lean statements

`PrefixHull.lean` imports only `GraphRegion`; it does not import the candidate
executable connectivity proof. The following general statements compiled:

| Statement | Kernel-checked conclusion | Axioms reported |
|---|---|---|
| `hull_connected` | Any two members of `Hull r terminal` have the required `Walk` | `propext` |
| `package` | A nonempty finite list equal in membership to a prefix hull constructs `ConnectedSupport` | `propext` |
| `package_exact_membership` | `toRootedRegion` keeps the supplied list membership | `propext`, `Classical.choice`, `Quot.sound` |
| `package_consumer` | The imported deepest-root consumer applies under its depth and overlap hypotheses | `propext`, `Classical.choice`, `Quot.sound` |

The package premise is explicit membership equality with the prefix hull.
It is not an axiom asserting extraction correctness. This arm has not
instantiated that premise for arbitrary `minimalVertices` in Lean. All nine
hand controls, all four rejection controls, and the first and last sweep
proofs had no axiom dependencies in the printed audit. No proof code uses
`sorry`, `admit`, a custom axiom, or `native_decide`.

Verbatim sample from `prefixhull-build.log`:

```text
'PrefixRoute.hull_connected' depends on axioms: [propext]
'PrefixRoute.package' depends on axioms: [propext]
'PrefixRoute.package_exact_membership' depends on axioms: [propext, Classical.choice, Quot.sound]
'PrefixRoute.package_consumer' depends on axioms: [propext, Classical.choice, Quot.sound]
```

`RMAF.olean`, `PureBridge.olean`, and `GraphRegion.olean` were freshly built
from their unchanged source files into this arm's `build/` directory before
imports. Lean ran through `./bootloops-lean`, version 4.35.0, commit
`eb6cafb7290e8bd5f2937522d8d804f58f02bafc`, arm64-apple-darwin24.6.0.
The source hashes and output hashes are in `MANIFEST.json`.

## Timing and replay

The pilot generated 176 comparisons in 0.047443666 seconds and compiled
with Lean in 0.56 seconds. Before the larger run, the journal recorded a
rough 2.60-second compile projection from its 4.64-fold case-count increase,
with comparable term sizes assumed. The 816-case file compiled in 1.98
seconds. Timing measures wall-clock execution here and implies no algorithmic
complexity bound.

| Step | Wall seconds |
|---|---:|
| Fresh RMAF dependency | 5.62 |
| Fresh PureBridge dependency | 0.46 |
| Fresh GraphRegion dependency | 0.37 |
| 176-case pilot plus controls | 0.56 |
| 816-case sweep plus controls | 1.98 |
| General prefix-hull proof | 0.41 |
| Two expected false-proposition failures | 0.34 |

Run `sh research/rmaf/bridge_review/executable/prefix_route/replay.sh` from
any directory to rebuild the dependencies and repeat the complete bounded
check. The script checks that both deliberately false assertions fail for
the expected reason. `prefix_check.py` includes its purpose, applicability,
output meaning, and acceptance controls; it is a one-shot independent review
instrument, not a replacement toolkit implementation. `RESULT.json` records
the measured counts and formalization boundary. `JOURNAL.md` preserves the
initial skeleton, source-reading notes, and pilot launch decision.

The complete `./bootloops-check` toolkit battery was not run in this arm;
no toolkit code was changed. All required local Python and Lean engines
were available. The graph proof and exact comparisons were executed with
their retained logs; completion status alone is not used as acceptance.

## Sources and independence

Read facts, with exact local source locations:

- `RMAF.lean:8–15` defines trees and their leaf labels; `109–133` defines
  addresses, prefixing, rooted spans, and minimal vertices. The branch at
  line 131 is `if ls.isEmpty then prependSide true (minimalVertices selected r)`.
- `GraphRegion.lean:9–14` defines adjacency and walks. Adjacency is
  `(∃ b : Bool, v = u ++ [b]) ∨ (∃ b : Bool, u = v ++ [b])`.
  Lines 87–112 define connected support and its membership-preserving
  region; lines 123–127 expose the consumer with depth and overlap premises.
- `PureBridge.lean:10–31` defines address, rooted region, and the original
  deepest-root consumer.

The occurrence/LCA characterization and case analysis in `DERIVATION.md`
are deductions from those definitions. No external mathematical statement
or literature claim is imported. Toolkit consultation covered the complete
package index and the external index's Lean/proof-assistant/graph/tree terms;
no existing package implements this tree-address comparison. A fresh
implementation was required by the independent-route assignment.

The shared layers are the target, the unchanged executable definitions,
the graph interface and its permitted theorems, list-prefix mathematics,
the local machine, and Lean/Std. These checks can expose errors in recursive
span extraction, child-address mapping, LCA suppression, and occurrence
handling. They do not independently validate Lean's kernel or the shared
address convention. The evaluator's algorithm, graph traversal, generated
expectations, and prefix-hull proof were written in this arm without reading
`executable/lean/ExecutableConnectivity.lean`, reviewer code, or any existing
Python geometry/oracle implementation. No other proof agent was steered.

The hand controls were written before source inspection and used only as
fixed acceptance checks. The evaluator had no corrections based on failed
mathematical outputs. A later source audit initially matched the word
“axiom” in an explanatory comment; inspecting the exact match and excluding
comments left no prohibited proof declaration. No expectation or proof
statement changed in response.

The acceptance check uses exact finite address sets, so floating precision,
held-back numerical digits, and fit leave-one-out tests do not apply. The
independent Python construction and Lean evaluation share the mathematical
address convention, which limits their independence as stated above. The
receipt received separate honesty/count and sentence-clarity passes; it
retains the general formalization gap in its opening statement.
