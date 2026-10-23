# Fresh index-route review

The independent finite-index route is **CONFIRMED for its stated supporting interfaces**. It constructs a complete duplicate-free enumeration, preserves every surviving child index, identifies exactly the two designated boundary indices, and proves its count and closed-list equations. Its family consumer is conditional on an existing parent family and equalities for that family's finite enumeration and boundary. This review supplies no geometric family constructor, adapter to the main merged-index representation, child restriction, complete transition correspondence, or full G2 result.

I froze and executed a new finite-index checker before opening the index proof or author checker bodies. I then read all of `IndexRoute.lean`, rebuilt its old local dependencies and proof in a new isolated directory, checked all 28 actual axiom outputs, and compiled the frozen positive/false controls and a conditional consumer. The previously completed merge/geometry review, its source files, receipts and reports remain unchanged. This separate addendum completes the index review described as pending in the preserved checkpoint.

## Accepted interfaces

`survivors` (`IndexRoute.lean:12`) recursively removes the designated member and returns actual values of the subtype `{x // x ≠ o}`. The proofs at lines 42–95 establish exact membership, absence of duplicates, deletion of exactly one member under nodup/membership hypotheses, and equality of forgotten subtype values to the filtered source list. These are direct list proofs; the route does not invoke the old private deletion lemma or `cost_counts_closed_indices`.

`Joined` has one boundary constructor and separate left/right survivor constructors (17–21). `mergedFinite` (134–138) fills all three old `FiniteIndex` fields: actual elements, nodup and completeness. Its enumeration puts the new boundary first, followed by left survivors and then right survivors in source order. The whole-child maps are injective within each child, jointly cover `Joined`, and satisfy:

> `fromLeft o p x = fromRight o p y ↔ x = o ∧ y = p`

That theorem is `only_boundary_identified` at lines 218–222. Equal-looking names in opposite children remain distinct unless they are the designated pair.

The route proves merged length `a.elems.length + b.elems.length - 1` (176–182), closed length `(a.elems.length - 1) + (b.elems.length - 1)` (184–191), and exact ordered equality after filtering out the new boundary (232–240). With actual child families whose boundaries are `some o` and `some p`, `family_closed_count` gives closed length `L.cost + R.cost` (255–260).

The consumer theorem at lines 270–290 explicitly requires:

> `(G : Family (.node l r) (Joined o p))`
> `(hfinite : G.finite = mergedFinite L.finite R.finite o p)`
> `(hboundary : G.boundary = some Joined.boundary)`

It concludes the block-count equation, the exact ordered `G.closedIndices` list, and the cost sum. These assumptions already supply an actual geometrically valid `G`; they are appropriate for a conditional arithmetic theorem and do not prove that such a family exists. My compiled `ConsumerProbe.lean` retains these same premises and extracts the cost and closed-list conclusions. `#check @family_consumer_equations` prints the complete type in the retained compiler log. No adapter to `Transitions.MergeIndex` is defined or used.

## Fresh controls

The independent checker forms tagged source atoms and unites only the two boundary atoms into one class. It validates conservation of all source atoms, unique ownership, the exact boundary class, and singleton classes for every survivor. This differs from using the author recursive subtype-list code; no author Python checker or runner was read or imported. The shared layers are the frozen fixture specification, ordinary finite-index semantics, and Python standard-library data structures.

| Registered controls | Executed result |
| --- | --- |
| Positive index fixtures | All 5 exact ordered lists and count pairs accepted: (1,0), (2,1), (3,2), (4,3), (4,3) |
| Malformed indices | All 3 rejected; all 3 linked clean fixtures accepted |
| Wrong numbers | All 4 rejected; all 4 correct twins accepted |
| Extra planted corruption | Coalescing same-named nonboundary left/right survivors rejected; clean partition accepted |

The separate false-proposition run asserted that the corrupted survivor partition was valid. It exited with an assertion identifying `survivor class is not singleton`, after the clean assertion passed. The one-fixture pilot took 0.000100625 seconds internally; the complete fixed battery took 0.000175667 seconds internally. These timings exclude wrapper startup. No larger census was run.

The JSON lists declare their own finite source universes. Their tests do not establish completeness against an arbitrary Lean type; the universal `FiniteIndex.complete` proof at lines 125–138 supplies that interface. Finite fixture checks are evidence for the checker and interpretation, not a substitute for the universal proofs.

Checker SHA256: `5e9e0c9e40e13790c46e7895098bdddbb5444ec5a19a7870ab3f3c80b2f6c6d3`.
Controls SHA256: `79b3d2d0109044b94547cab61be15b34e954596710a3fb840a519e68cc2bb209`.
Neither file changed after the checker freeze.

## Kernel execution

`./bootloops-lean` reported Lean 4.35.0, commit `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`, on arm64-apple-darwin24.6.0. `ELAN_HOME` was the workspace `.runtime/elan`; `LEAN_PATH` contained only this review's new snapshot. All local `.olean` files were rebuilt from source. Snapshot source hashes matched the author's final generated manifest, and the live `IndexRoute.lean` matched its snapshot.

| Module | Actual axiom-query outputs | Observed axiom union |
| --- | ---: | --- |
| TripleDP, old dependency | 19 | propext, Classical.choice, Quot.sound |
| ConnectedRegions, old dependency | 8 | propext, Quot.sound |
| FamilyAssembly, old dependency | 17 | propext, Classical.choice, Quot.sound |
| IndexRoute | 28 | propext, Quot.sound |
| ConsumerProbe, reviewer-only | 1 | propext, Quot.sound |

Every actual `IndexRoute` output name matched the corresponding source query in order. The 28 queries include the `mergedFinite` definition; they are not a total of new mathematical theorems. The positive/negative control files contain no axiom queries. Source scans found no proof placeholders, custom axiom declarations, `native_decide`, `unsafe`, or `implemented_by` in the rebuilt chain or reviewer probe.

All five frozen Lean fixtures compiled as ten exact list/count propositions. The original three-way clean conjunction compiled. The three false files failed specifically at `singletonEnums.length = 2`, `singletonClosed.length = 1`, and `collisionLeft = collisionRight`. Three separately compiled files with identical imports and correct values/polarity passed. A new missing-import control failed before checking its proposition and was excluded from mathematical rejection evidence. This followup required no reviewer harness or proof correction.

## Index report rulings

These locations refer to the preserved index `REPORT.md`, SHA256 `0128f4e3411f166d8ab9c6cdd115f1b487705db05174e5859641ef3407493f75`.

| Use site | Ruling and source |
| --- | --- |
| Lines 3–13 | Actual finite-index construction under decidable equality on both child index types: confirmed by source 12–29 and 134–138. Historical pending-review status is superseded only by this addendum. |
| Table line 20 | Exact survivor membership/nodup/deletion: confirmed at source 42–88, with the stated nodup and designated-membership premises. |
| Table lines 21–23 | Complete/nodup output, retained membership and separate injections: confirmed at 120–174. |
| Table lines 24–26 | Whole-child injection, only-boundary identification and joint surjectivity: confirmed at 194–230. |
| Table line 27 | Exact merged count: confirmed at 176–182. Child completeness supplies membership of each designated member. |
| Table lines 28–29 | Closed membership and exact ordered filter equality: confirmed at 168–174 and 232–240. |
| Table line 30 | Survivor values equal actual child closedIndices: confirmed at 244–248, using the child boundary equation. |
| Table lines 31–32 | Actual child cost sum and boundary charge: confirmed at 255–266. The cost-sum theorem requires both designated child boundaries. |
| Table line 33; lines 35–40 | Family consumer conclusions: confirmed only with actual G, hfinite and hboundary. Missing geometry/existence and representation adapter are correctly stated. |
| Lines 42–50 | Final receipt exists; all copied-source hashes match. Fresh rebuild independently confirms 28 exact query names and standard axioms. The stated 3.655368333000297 seconds is retrieved author-run timing, not this review's timing. |
| Lines 52–59 | Control hash, five positive count pairs, three exact false goals and correct twins: independently reproduced. |
| Lines 61–66 | Author Python receipt records 5 positives, 3 malformed inputs, 4 wrong results and a detected broken comparator. Those are retrieved author observations; the independently frozen checker above supplies separate fresh evidence. |
| Lines 68–76 | Failed author attempts are historical provenance, excluded from accepted proof evidence. The final source and fresh output contain no sorryAx. This review did not replay failed development versions. |
| Lines 78–85 | Import/code inspection confirms shared old FamilyAssembly definitions and an independent local deletion/count proof; neither main transitions nor geometry route is imported. The author's no-cross-reading history is reported provenance, not a kernel-verifiable fact. |
| Lines 87–98 | The listed author replay scripts exist and match their manifest hashes; they were not used by this reviewer. The general BootLoops numerical suite was not run here either; scoped proof/control checks were executed. |

## Checkpoint rulings

These locations refer to the preserved `CHECKPOINT.md`, SHA256 `467ed973dd8e27b9e621afe290c82eecbc77933e9984734d8c26820d25ab7bdf`.

| Use site | Ruling |
| --- | --- |
| Lines 3–9 | Exact main merge and all family fields: supported by the unchanged completed main review and its compiled existential consumer. This index followup adds no geometric conclusion. |
| Lines 11–19 | Historical report/pin preservation, fresh graph controls, four false Lean goals with correct twins, import-error exclusion and standard axioms: match the preserved completed review and receipts. All their recorded hashes were rechecked. |
| Lines 21–26 | Main query counts 4/9/7/15 and reviewer query 1 match actual earlier receipts. Their distinction from a new-theorem count is correct. |
| Lines 28–29 | Geometry's 17 support statements and explicit left-root correction match the completed review and source. |
| Lines 30–35 | Separate index enumeration, only-boundary identification, count and closed-cost length: confirmed here under the opening two-boundary scope. No adapter is asserted or proved. “Fresh review … is pending” is the historical checkpoint state; this separate addendum completes it. Main imports neither supporting route. |
| Lines 37–41 | Restriction is a separately assigned open task. File existence and the assignment are provenance, not a new scientific result of this review. The leafless-incursion scope distinction agrees with the already accepted `FamilyGeometry.normalized_open_child_occupied`/`normalized_open_no_leafless_child` interfaces at lines 29–43. This followup did not audit the new restriction target or proof. |
| Lines 42–44 | Normalization transport, legality, graph/Python links and broader algorithmic claims remain outside the accepted merge/index interfaces. No stronger result follows from this review. |
| Lines 46–50 | Independently rechecked the cited baseline: all 168 pinned files match, with zero mismatches and the same baseline SHA256. General toolkit validation remains explicitly unrun. |

`GEOMETRY-PREMISE-NOTE.md`, SHA256 `38c28c537d660e966f9410819009419cea9fc2e09eeda5c87c198b970b3bd5d7`, correctly states the premise and its intended use at lines 3–7: `jointSupport_rootPaths` needs `s []`; the intended two-boundary case supplies it. Lines 9–14 correctly describe the main proof's old decomposition dependency, absence of geometry-route imports, and preservation of the original source/report. No source repair or further geometry claim is required.

## Preservation and limits

`IndexRoute.lean` SHA256 is `f4a0a1b987f4e8084c81e9c352c9a1998eefba15d1f94d01a2b74919e87e3a4a`. `SOURCE-MANIFEST.json`, `AUDITED-SOURCES.json`, and `FINAL-SHA256.json` retain the exact source/report versions, controls, commands, outputs and review-file hashes. Canonical results use `research/rmaf/results/triple-family-transitions-fresh-index-*`.

The earlier review's complete hash manifest, the old `REPORT.md`, and `MAIN-MERGE-SHA256.json` remain unchanged. I neither edited the new checkpoint nor investigated the active restriction proof task. No author checker code was read or reused, no child agent was spawned, and no aggregate theorem total was computed. The old semantic definitions and Lean/Std remain shared trusted layers; this separate route is fresh verification of the stated finite-index interfaces, not an independent reconstruction of Lean or all prior family semantics.
