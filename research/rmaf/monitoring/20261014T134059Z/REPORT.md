# Connectivity of the existing minimal-vertex extractor

Lean proves that the unchanged `RMAF.minimalVertices S t` is connected under
the binary-address graph used by `BridgeReview.Walk`. A selected label that
occurs at a leaf makes the output nonempty. The proof constructs the existing
rooted-region interface with exactly the extractor's vertices and composes
with `PureBridge.deepest_root_in_neighbor`. A fresh rebuild and semantic
review confirmed this exact interface. Leastness of the support,
unique-label interpretation, source/target restriction transport, and the
remaining pure-bridge exchange assumptions remain open.

The statement covers every `RMAF.Tree` and list of selected natural-number
labels, including repeated labels. Addresses are lists of Boolean child
choices, with `false` for left and `true` for right. An edge adds or removes
one final choice. An empty output satisfies the pairwise connectivity
predicate vacuously; constructing `ConnectedSupport` separately requires a
nonempty output. The theorem
`minimalVertices_nonempty_of_leaf` supplies that requirement from
`x ∈ leaves t` and `x ∈ S`.

The new declarations are in `lean/ExecutableConnectivity.lean`:

| Declaration | Exact content |
|---|---|
| `rootedSpan_walk` | Every emitted rooted-span vertex is reachable from `[]` through emitted vertices. |
| `minimalVertices_connected` | Any two vertices returned by the existing extractor have a walk inside that output. |
| `minimalVertices_nonempty_of_leaf` | Actual occurrence of a selected label implies nonempty output. |
| `extractedSupport_exact` | The constructed support's full list equals `minimalVertices S t`. |
| `extractedRegion_exact` | Region membership is equivalent to membership in that same list. |
| `deepest_extracted_root_in_neighbor` | If two nonempty outputs overlap and the first has a root at least as deep as the second, the first root belongs to the second output. |

The proof first establishes root-to-vertex walks for `rootedSpan` by induction
on the input tree. Prepending a fixed side preserves graph edges. Each child
walk therefore lifts into its parent's address coordinates, where the edge
from `[]` to the child root completes the walk. The proof then follows the
three branches of `minimalVertices`: recurse into the right child, recurse
into the left child, or retain both rooted spans and the parent root. These
branches preserve connectivity without assuming convexity, ancestry, or
correctness of the extractor.

The constructor uses the extractor's head and tail and proves that
`head :: tail` is the original list. The previously reviewed graph theorem
chooses the shortest support address and derives the `below` and `convex`
fields required by `PureBridge.RootedRegion`. No degree-two vertex is removed
at this conversion. In the final theorem, nonemptiness, depth ordering, and
overlap are the only geometric hypotheses left to the caller.

The five hand controls were frozen before reading the executable definitions
and before constructing the general proof. For `t = ((0,1),(2,3))`, Lean
checked the exact lists for selections `{0,2}`, `{1}`, `{0,1}`, the empty list,
and the absent label `{9}`. The controls also prove that deleting `[false]`
from the crossing support changes the output and disconnects the retained
root from `[false,false]`. Separate Lean files deliberately assert the
deleted support is correct and the absent selection is nonempty. Both fail
with an explicit `decide` falsity diagnostic. The corresponding true
statements compile.

`audit.py` rebuilt `RMAF`, `PureBridge`, and `GraphRegion` from their unchanged
sources into a fresh dependency directory, then compiled the new controls
and proofs. It checked 24 new named theorems: 17 interface/helper theorems and
7 control theorems. Its 26 new axiom reports include the two constructors;
their dependencies are limited to `propext`, `Quot.sound`, and
`Classical.choice`. Source checks exclude placeholders, custom axioms, and
`native_decide`. The run took 8.005 seconds, including dependency builds.
`audit/certificate.json` records the source hashes, every build log, and each
axiom inventory.

The audit separately tests its negative-result parser. Five frozen diagnostic
cases include an explicit false proposition, a successful exit, a synthesis
failure, an unknown identifier, and a mixed false/unknown-name failure. Only
the explicit false proposition with a failing exit receives falsity credit.
A real malformed Lean proof also fails and is rejected as a falsity receipt.
This prevents an elaboration error from masquerading as a passed negative
control.

The fresh reviewer rebuilt the dependency chain independently, restated the
exact walk theorem, and compiled a direct call to the original consumer.
Nine frozen hand cases and 816 further exact extractor comparisons passed;
separate graph traversal checked connectivity in all 816 finite cases. The
review also checked positive, false, and malformed proof diagnostics, five
hostile parser mutations, unchanged source hashes, and 81 standard-only
axiom reports across the dependency chain and review declarations. The
reviewer's first diagnostic-parser mismatch failed closed and remains in
its logs. A subsequent complete replay passed after the parser repair.

Two further agents derived the extraction behavior without reading the
candidate proof. The prefix route reproduced nine hand cases, rejected four
corruptions, and compiled 816 further exact membership comparisons. It also
proved generic prefix-hull connectivity in Lean. Its general equality
between the extractor and the prefix hull is a written structural argument,
not a second Lean proof of that equality. The edge-cut route reproduced 12
hand supports with a separately written edge-deletion construction and
kernel-checked source comparisons; three corrupted supports failed for
actual falsity. Its general correspondence argument is also written
mathematics. These finite panels overlap, so their counts are not summed as
unique coverage. The universal executable connectivity result rests on the
structural Lean theorem in the main proof file.

The interface trace is deliberately narrow:

| Original use | Result supplied here | Remaining obligation |
|---|---|---|
| `PureBridge.deepest_root_in_neighbor` needs two `RootedRegion` values. | `extractedRegion` constructs them from the actual extractor, with exact membership. The composed theorem is kernel checked. | Caller supplies nonemptiness or selected-leaf witnesses, the depth comparison, and overlap. |
| Pure-bridge graph semantics uses minimal source-component embeddings. | Connectivity and a vertex-preserving region realization are established for the executable output. | Formal leastness, valid ambient-tree/leaf interpretation, and the intended component-label correspondence are not supplied here. |
| `ExchangeSystem.freeLeft`, `freeRight`, and `clearRest` need compatibility and a one-cut repair. | No new fields of `ExchangeSystem` are constructed. | Degree-two split transport, old-mark preservation, and complete exchange realization remain open. |
| Marked-region role swap and the running-time argument need family equivalence and parameter bounds. | No new family equivalence or algorithm bound is asserted. | Source/target restriction transport, the remaining G2–G7 interfaces, safe cover, and the prior-bound audit remain open. |

For outputs from different trees, overlap here means equality of Boolean
addresses. The theorem supplies no source/target vertex correspondence.

The candidate proof, audit, and hand controls share the same target statement,
executable definitions, graph definitions, and Lean toolchain. The audit
reuses the earlier graph audit's source-hash and axiom-parsing pattern; it is
a replay check, not an independent mathematical derivation. Fresh semantic
review and the two geometric checks use separate code and frozen controls.
The reviewer and prefix route share prefix-hull mathematics; the edge-cut
route uses edge separation. Their receipts are `fresh_review/REVIEW.md`,
`prefix_route/RECEIPT.md`, and `edgecut_route/REVIEW.md`. All routes share the
address convention, source definitions, and Lean/Std. No novelty or
faster-bound claim follows from this result.

Reproduce the typed interface and diagnostic checks from the workspace root:

```sh
./bootloops-python research/rmaf/bridge_review/executable/audit.py
```

The first failed elaboration and its successful repair remain in
`audit/connectivity-attempt1.log` and `audit/connectivity-attempt2.log`.
The failed attempt concerned Boolean-parenthesis and simplification details;
it is not counted as a proof. `development/Probe.lean` records exploratory API
checks and is excluded from production builds. The completed graph-support
checkpoint and its evidence were preserved unchanged.
