# Second independent local-chain review

## Status
Started 2026-10-14. Independent reconstruction and controls precede reading author/reviewer proofs. No prior evaluator imported. Owned paths: repair/review2/, results/thesis-correctness-repair-review2-*, progress/thesis-correctness-repair-review2.json.

## Inputs read
- SECOND-REVIEW-TARGET.md (first)

## Planned evidence
1. Required protocols and precise statements; primary thesis pages.
2. Fresh graph/cut/yield semantics and planted/corrupted controls.
3. Independent corridor derivation and exact frozen witnesses.
4. Read delivered proof reports, inspect per-use-site assumptions.
5. Rebuild unchanged Lean constituents and negative controls.
6. Scope-limited report and machine-readable receipt.

## Independent reconstruction
Pending.

## Controls
Pending.

## Proof audit
Pending. Proof reports unread.

## Remaining obligations
General protected-origin graph lift and other global claims excluded.

## Protocol and tool choice
Read the six assigned skills and toolkit index. The index contains no rooted-agreement-forest cut/yield checker; generic graph/algebra packages do not implement the thesis rho-root convention. The task additionally forbids author/reviewer evaluator reuse, so the needed independent, one-shot exact checker is justified. It will enumerate F1 cut-yields to certify AF membership, and explicitly contract F2 graphs while preserving original-edge provenance. Control expectations are frozen in CONTROL-PLAN.json before execution. No reusable toolkit or upstream file is modified.

Read PROOF-TARGET.md, SECOND-EXCHANGE-TARGET.md, two-stage-original-spec.json, and frozen compound/partial boundary fixture data only. No construction/proof reports or evaluator sources read yet.

## Executed controls and independent fixture reconstruction
`fresh_graph.py controls` ran before target fixture evaluation. Returned identical optimum 0, single-rearrangement optimum 1, exact single-cut components, null preservation and singleton all-cut yield; wrong topology and unchanged suppressed-edge claims were rejected.
`fresh_graph.py frozen` reproduced both cutsets with exact counts 2→3→2, final cuts eb1,eb2, optimum 2, and both detached-rho variants (rho singleton and component alone). Both intermediate and final yielded forests were actual AFs by exhaustive F1 cut-yield membership. Dropping either final pendant cut failed AF. The corrupted unchanged claim for corridor edge e:n00 failed.
`fresh_graph.py boundaries` reproduced compound-empty failure (E has 3 cuts, optimum 1, c root fragment empty, normalized output not AF) and partial-restoration failure (E has 2 cuts, optimum 1, partial output not AF, full normalization AF). Neither is a minimum-consumer counterexample.
Measured first geometry pilot: 100 arbitrary K cases over 10 graphs in 0.0159259159991052 seconds. This pilot contains atomic endpoints only, so a larger pilot spanning compound endpoints follows before the full finite family. Proof reports remain unread.
Second pilot: 1,000 cases over 20 graphs, including compound endpoints, ran in 0.1898453329995391 seconds; 220 cases had an empty u or x fragment. The complete current family has 15,600 cases (same bounded vertex sizes and code), projecting a few seconds from this measured pilot, conservatively under one minute. Proceed with full family; finite no-fire remains a finite check, not a proof.

Completed independent arbitrary-K geometry run: {'cases': 15600, 'elapsed_seconds': 3.515246417002345, 'empty_root_cases': 4560, 'graphs': 36, 'limited': False, 'second_cut_counts': {'0': 3900, '1': 7800, '2': 3900}}
All target-controlled reconstruction and own derivation now precede first reading of proof reports.

## First delivered-supplement audit
Read review/LOCAL-RECONSTRUCTION.md only after the independent reconstruction receipt above. Its corridor supplement matches the independently recorded geometry derivation: exact B, no corridor cuts after first full normalization, unchanged ex/eu/optional parent, nonminimum intermediate allowed, and cardinality 2+|residual|. The supplement explicitly leaves construction of the starting minimum E0 from sequential branches open. No disagreement found at this stage; finite checks alone are not the reason for accepting the geometric argument.
Read review/REPORT.md after LOCAL-RECONSTRUCTION.md. Its local/global boundary is consistent with the target: no AF theorem is claimed for the Lean walk/list constituents, the intermediate is not assumed minimum, and the final partial-restoration formula is not asserted identical to full normalization. Reported first-review counts are retrieved only; they are not part of this review's independent numerical evidence.
Read component_route/PROOF.md. Section1's partition criterion is sufficient because all labels are assigned and each disjoint minimal embedding root can be separated without cutting another block's hull. Section2 carries the often-omitted endpoint stem. Section3's one-cut outside attachment requires the anchor exactly where needed; >=2 cuts separate outside labels by actual eu or have no outside labels at a root. Section4's repair restores all internal cuts, and the binary two-branch lower bound gives strict decrease. Sections5–6 explicitly use global-current minimum and propagate survivors rather than reapply minimality to the intermediate. The remaining edge representation in this version is supplied only by the independently audited corridor supplement, not by its semantic-composition paragraph.
Read edge_route/CONSTRUCTION.md and unchanged OriginalEdges.lean/RootedPaths.lean. They establish provenance/count/walk statements with explicit boundary and anchor assumptions; none asserts AF preservation. `full_to_partial_inclusion` requires parent_kept, so it does not hide the failed unconditional partial restoration. Independent local-hunt pilot: 10/225 ordered pairs and 30 compatible whole/rho-detached active pairs, 2,312 AF cutsets in 0.1258017079999263 seconds. A full 225-pair run projects under 5 seconds at these sizes; allow up to one minute. This is a post-proof-read hostile check, not a new independent source of a universal theorem.

## Formal rebuild and source rendering
All eight unchanged positive Lean modules rebuilt in review2/lean-build under Lean4.35.0. Both deliberate false controls were rejected. Printed dependencies are subsets of propext, Classical.choice and Quot.sound; a supplementary print covers parent_rank, which the original control module did not print. All source copies match their original hashes. Exact formal scope is in lean.json; none is a universal AF theorem.
The four-leaf local hunt returned 51,516 AF cutsets over 675 compatible active pairs, 44,862 N_anchor applications (43,755 nonminimum), 42,204 both-survivor cases, 5,070 strict repairs and 9,897 minimum-fragment instances. No failure. It found zero ordinary/swapped optimum-exchange premises in that four-leaf family, so that denominator supplies no exchange evidence. Additional five-label controlled consumers are needed below.
The bootloops Python lacks fitz; use bundled Poppler for read-only primary PDF rendering. No unavailable engine is concealed. No toolkit-wide bootloops-check run has been made.

## Version2 order boundary
After completing the own corridor derivation, frozen exact reconstruction, full arbitrary-K run and reading the already-delivered supplement, inspected the completed `thesis-correctness-repair-edge-second-summary.json` receipt. It reports LOCAL-CERTIFICATE-PROVED-GRAPH-ENCODING-OPEN and points to its delivered REPORT.md. Only now is reading version2's proof/report allowed. Its reported counts are retrieved, not adopted as this review's evidence.
Version2 REPORT.md and all three production Lean files plus controls read after the completed receipt. Its two-splice geometry matches the independent derivation. `MarkedTree` deliberately permits arbitrary marks and does not encode reduced binary parent-graph validity, unique IDs, or graph-yield correspondence: construction of the two witnesses and encoding correctness remains a real formal premise. `two_splice_root_component` compares the evaluator's attached root component; its use for raw graph fragments still needs that correspondence. `secondCut` requires the caller to supply actual ex/eu/ev IDs and parentPresent; the binary geometry supplies those in prose. No new mathematical defect found.
Consumer pilot: six five-label pairs in 0.030890792000718648 seconds, no eligible exchange premises yet. Full 90-pair fixed family projects below one second at the measured size. Exact final-node and edge-provenance comparisons were added to the arbitrary-K checker; rerun is warranted by this additional identity question. A supplementary 10-label family tests arbitrary cuts inside detached pendant subtrees (same representation, bounded at 32,768 cases), measured runtime unknown initially and limited by a 30-second shell yield.

## Completed supplemental checks
Five-label consumers: 90 active-pair cases, 36 ordinary-c and 36 swapped-a exchanges, 38 common-uncle two-stage minima, each 2→3→2. Supplementary arbitrary-K cuts inside pendant subtrees: 16,384 cases including 15,360 with internal pendant cuts, all checks passed in 5.213492082999437 seconds. This supplemental larger-size run was bounded but not separately piloted; disclosed as a timing-protocol limitation rather than retrospectively claiming a pilot.
The repeated 15,600-case geometry check included additional exact equality of surviving original vertices, labels and final edge path provenance. No failure. Initial before-proof geometry assertions checked labelled rooted topology, unchanged edge IDs/endpoints, fragments and counts; the stronger final-ID assertion was added after proof reading and is labelled accordingly.
Version2 unchanged ParentTransport, YieldTransport, SecondCut and PositiveControls rebuilt; its false retained-corridor NegativeControl was rejected. Extra prints of lower_splice and upper_splice report no axioms. Source hashes match the delivered receipt.
Rendered primary PDF pp102,113,116 and inspected the actual mathematical formulas. Source ledger contains 15 printed pages and seven exact extraction strings. Bibliographic identity is local title-page only; no external audit or bibliography entry addition.

## Report checks
Two prose passes checked quantifiers, source attributions, numeric denominators, formal/prose distinctions and opening scope. Corrected the possible implication that a minimum original cutset containing B alone proves arbitrary residual-optimum equality. Referee framing of the prior reports is recorded in referee_sim_prior_reports.md; this agent is a fresh nonauthor of those reports, not of its own report. Arithmetic is exact, so numerical-precision/held-out-digit conditions are inapplicable; known-answer and corruption checks supply the relevant acceptance structure. No scientific claim rests on exit status alone.

## Delivery
Completed local review; REPORT.md and verdict.json state the exact accepted prose scope, separately rebuilt Lean statements, broader-statement failures, and remaining general lift. All assigned result/progress outputs are written. No parent/author source, previous receipt or aggregate theorem count was modified.
