# Fresh referee review of executable report

Reviewed snapshot: `REPORT-reviewed-01.md`, SHA-256 `a72c4f53476558e1277d95de8dc3c79748d5bd6dc879f941e87ed87dc2430ca9`.

The reviewer authored none of the candidate proof or report. The review independently rebuilt the source chain and executed the controls documented in `REVIEW.md`. This table concerns the report's scientific meaning; the separate source audit establishes the formal interface.

| Audience | Strongest standard objection | Axis | Answer in reviewed report | Severity / action |
|---|---|---|---|---|
| Lean/formal verification | The proof may certify a surrogate hull or accept connectivity as a structure input. | Correctness | Lines 3–7 and 25–30 identify the original extractor and exact membership. Fresh `InterfaceAudit.lean` confirms the complete typed chain without geometric premises. | Answered. |
| Lean/formal verification | A routine rooted-tree lemma is being sold as a new theorem. | Novelty | Lines 85–91 explicitly make no novelty claim; the title names a specific existing extractor. | Answered. |
| Graph algorithms and rMAF | Boolean addresses from different trees do not identify the same biological or graph vertex; the two-tree theorem could be mistaken for transport. | Correctness | Lines 9 and 81–83 leave transport and interpretation open, but the consumer row does not spell out address-only overlap. | Low: add one sentence saying cross-tree overlap is equality of Boolean addresses and supplies no vertex correspondence. |
| Graph algorithms and rMAF | Connectivity is elementary and does not prove a faster algorithm, full G1, leastness or equivalence with the paper model. | Novelty | Opening lines 8–10 state leastness/interpretation/transport remain open; rows 81–83 and lines 90–91 exclude algorithm and novelty claims. | Answered. |
| Verification and reproducibility | The independent review may merely repeat the author's oracle or treat any compiler failure as successful refutation. | Correctness | Lines 68–74 address diagnostic specificity; lines 85–90 disclose shared definitions/toolchain. Fresh review additionally uses its own leaf-address hull and BFS, retained wrong-twin/malformed tests, and a logged parser failure/repair. | Answered for the reviewed checks; update pending status only after linking reviewer evidence. |
| Verification and reproducibility | “Independent” overstates a second wrapper around the same Lean kernel and mathematical model. | Novelty | Lines 85–90 distinguish replay from independent derivation. Fresh evidence must retain that distinction when inserted. | Answered; no independent-kernel or independent-mathematics claim is licensed. |
| Practitioner using the consumer | Empty selections, absent labels, or duplicate leaf labels may invalidate the promised support constructor. | Correctness | Lines 12–19 explicitly separate vacuous connectivity from nonempty construction and require an actual selected occurrence. Frozen hand and finite controls cover all three. | Answered. |
| Practitioner using the consumer | A new wrapper may be presented as full operational graph realization. | Novelty | Lines 80–83 enumerate exact supplied interface and unsupplied exchange fields. | Answered. |
| General research reader | “Minimal” in the function name implies proven minimality, and “connected” might imply nonempty. | Correctness | Opening excludes leastness, and the second paragraph explicitly describes empty outputs. | Answered on the first reading path. |
| General research reader | The result implies scientific or algorithmic novelty beyond a formal bridge. | Novelty | Narrow title and opening scope, plus explicit line 90 disclaimer. | Answered. |

Required precision edit: lines 41–42 say the head and tail are concatenated. The head is a `Vertex` and the tail a `List Vertex`; the exact operation is `head :: tail`. Replace the sentence with: “The constructor uses the extractor's head and tail and proves that `head :: tail` is the original list.”

Opening reread last: the exact statement, selected-occurrence nonemptiness, consumer composition, pending review and unsolved stronger obligations are all present. No mathematical overclaim is identified. This verdict applies to the pinned snapshot, with the precision edit above and the suggested address-overlap clarification. Subsequent status/count edits need a checked diff.

## Final report revision

Final reviewed snapshot: `REPORT-reviewed-final.md`, SHA-256 `33479a00ddb6081588a53e642f033404937a58c7ecf4deb7661079ed4a7f0acb`. Both earlier wording changes are present. The final diff adds completed review status, the reviewer counts, the two other routes, and a more explicit independence statement. No remaining semantic or prose-integrity correction was found in that diff or the full reread.

| Audience | Final added claim checked | Evidence and ruling |
|---|---|---|
| Formal verification | Generic prefix-hull connectivity may be mistaken for a second proof of the complete executable theorem. | `PrefixHull.lean` proves `hull_connected`; `package` requires membership equality. The report explicitly says the arbitrary extractor/hull equality remains a written argument. No formal equality or full executable proof is attributed to that arm. |
| Graph/rMAF reader | The edge-cut construction might be promoted from finite controls into a formal universal graph-interface result. | The report attributes 12 finite support comparisons and three actual false controls, while describing its general correspondence as written mathematics. `lean-results.json` and the three opened false-control logs match those counts. |
| Verification/reproducibility | Duplicate test panels or shared mathematics could inflate independent coverage. | Reviewer and prefix panels both contain 816 cases of the same family. The report explicitly declines to sum them as unique coverage and names their shared prefix-hull mathematics and Lean/Std/source convention. |
| Practitioner/general reader | Added successful reviews might silently remove the stronger open obligations. | The opening still keeps leastness, label interpretation, transport and exchange assumptions open. The consumer still requires the printed hypotheses, and address overlap still supplies no source/target correspondence. |

The final count check independently recounted 9 `control_`, 4 `reject_`, and 816 `sweep_` statements in the prefix finite source; all agree with its result receipt. Every edge-cut JSON case compares exactly equal supports, and all three opened false logs contain the expected `decide` falsity diagnostic. Reviewer counts match the successful retained replay summary. These are receipt/attribution checks performed after the initial independent semantic review; no second-agent source was used to generate that review's expectations or proofs. No new proof run was needed because the five rebuilt proof source hashes still match.

The final prose passes checked the diff for exact claim strength, number units and provenance, then reread the whole report and opening. The generic-hull/general-extraction distinction is explicit where the new result is described. No visual typesetting certification is claimed for this plain Markdown review.
