# Root-path trimming: supporting proof

Lean 4.35.0 accepted a universal open-region trimming theorem in `PathStem.lean`.
The theorem proves label preservation, support shrinking, path convexity, and
exclusion of leafless child incursions. Full G2, closed-region trimming, the
four transitions, closing costs, the executable RMAF correspondence, and source
suppression remain open. Fresh external semantic and interface review is pending.

## Statement and proof

Addresses are finite Boolean lists, with the empty list as root. `RootHull L v`
means that some label address `a` in `L` has `v` as a prefix. For support `R`
and leaf predicate `leaf`, `openTrim leaf R` is `RootHull (leaf ∧ R)`.
The finite-tree specialization uses actual `BTree` vertices and leaf address–label
pairs; `LabelledTree` requires unique leaf labels. The geometric lemmas hold
without the uniqueness hypothesis.

For a root-containing path-convex support R, the accepted
`rooted_pathConvex_iff_prefixClosed` theorem implies that every prefix of every
label in R already belongs to R. Therefore `openTrim` shrinks R. Each label
witnesses its own membership, so the trim preserves exactly R's leaf labels.
A prefix of a retained prefix is retained; the trim is prefix-closed and thus
path-convex. A label witness also retains the root. With no label, the trim is
empty.

At any subtree root p, a retained descendant v has a label descendant a by
prefix transitivity. Conversely, any such a is itself retained. This proves
`rootHull_subtree_occupied_iff`. In particular, child occupancy is equivalent
to the presence of an original region label in that child. The direct
`openTrim_child_restriction` theorem identifies restriction of the trim with
trimming the restricted support and leaf predicate, including the empty case.

`rootHull_minimal` proves that the result is contained in every path-convex
support containing the root and the chosen labels. This characterizes the
minimal rooted support. Formal equality to a separately defined unrooted
minimal label span plus its root stem remains an additional interface lemma.
No unproved equality of these separately named objects is imported here.

`shrinking_preserves_disjointness` proves the pointwise fact for any indexed
family: simultaneous shrinking preserves disjointness. Applying root-path
trimming to every closed region would violate its root hypothesis; no theorem
here permits that application. Preserving region indices does not yet prove
nonempty blocks or closing-charge preservation for a complete family.

## Reusable interface

| Consumer need | Theorem | Remaining requirement |
| --- | --- | --- |
| Trim stays in original region | `openTrim_subset` | Original region is path-convex and contains root |
| Preserve actual leaf labels | `openTrim_preserves_labels` | Same hypotheses; given address is an actual leaf |
| Preserve nonempty open boundary | `openTrim_root_iff` | Region has a leaf label |
| Remove leafless child incursions | `openTrim_no_leafless_child` | No original label in that child |
| Restrict normalized open region | `openTrim_child_restriction` | Restrict both support and leaf predicate |
| Discard leafless fragment | `openTrim_empty_if_leafless` | No label; resulting support is empty |
| Preserve support disjointness | `shrinking_preserves_disjointness` | Each output is contained in its own input |
| Actual finite labelled tree | `finite_tree_open_trim` | Finite-tree membership, root, convexity, and label nonemptiness |

The root-containing case only proves a necessary normalization step for the
family transitions. It does not establish family restriction/assembly or the
relationship to the seven boundary states in the original DP.

## Executed evidence

Run from the workspace root:

```sh
sh research/rmaf/triple_dp/family/path_route/replay.sh
```

The completed replay used fresh dependency outputs in
`build-replay.62XrdR/` and retained logs and source hashes in
`../../../results/triple-family-path-replay.TpCi3w/`. The complete shell call
returned exit 0 after 2.302 seconds measured by the execution tool. The replay
printed this exact verdict:

```text
Lean proof accepted; seven concrete control theorem groups accepted; wrong proposition rejected with exit 1; matching clean twin accepted.
```

`path.log` prints the axiom dependencies of all 16 proved statements. Only
`propext` and `Quot.sound` occur; two statements use no axioms. The replay rejects
`sorryAx` and `error:` in accepted proof/control logs. It also checks the exact
false-proposition diagnostic, so an unrelated compile failure cannot satisfy
the negative control. The matched clean twin compiles in the same compiler.

The seven concrete theorem groups cover tree vertices, the known leafless
incursion pair, the known LCA-closed gapped support, the asymmetric four-leaf
pair, singleton-root labels, an empty label set, and adjacent same-color blocks
with an unused internal vertex. Several checks share a theorem group. These
checks retain the previously frozen cases; there is no census expansion.

The initial proof compilation failed because one root-path equivalence proof
left a disjunction unresolved. The initial concrete-control compilation failed
because Lean lacked a declared `Decidable OnPath` instance. Both diagnostics
remain in `triple-family-path-proof-v1.log` and
`triple-family-path-controls-v1.log`; their `sorryAx` diagnostics were rejected.
The accepted final compilation is independently rerun in the replay directory.

## Provenance and limits

The route read `FAMILY-TARGET.md` first, wrote `WORK.md` immediately, then read
only the allowed original proof modules and toolkit/skill instructions. It did
not read any new author-family module or other new route code. `WORK.md` froze
all controls and the false/clean twin before Lean proof code; its original hash
is checked by the replay.

All controls were visible to this author and are construction or regression
evidence. The asymmetric controls were newly authored before construction;
they are not held-out tests. The shared mathematical dependency is the accepted
address definition and rooted convexity theorem. The compiler and Std are
shared with the original proof. Rebuilding those sources checks dependency
integrity but supplies no independent semantic reconstruction.

No general BootLoops numerical suite was run by this arm: the changed files
are Lean theorem modules and a shell replay. No external engine was needed.
The measured compiler is ARM64 macOS Lean 4.35.0; cross-platform replay remains
unexecuted. The report underwent an author meaning/number check and a second
plain-language check. Fresh prose, semantic, axiom, control, and consumer review
belong to the parent campaign; this internal report is not an acceptance claim.
