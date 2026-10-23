# Fresh referee review of the checkpoint report

Reviewed file: `snapshot/family/REPORT.md`, SHA-256
`40e2d564024ed2302aa374bdfaf967fa19ae170b5219e06e35520d5d6296a306`.
This context did not author that report or any reviewed theorem. Fixes below
are recommendations for the parent, who owns the report; no author text was
edited. This is an internal formal checkpoint with no literature novelty claim.

| Audience | Standard objection | Axis | Answer at the expected reading location | Severity / action |
|---|---|---|---|---|
| Lean/formal methods | The theorem may merely assume a valid normalized output, or use untrusted axioms. | Correctness | REPORT:17–41 distinguishes input fields from constructed output proofs; :74–91 names axioms. Fresh isolated replay and the signature review support this. | Answered; retain the theorem hypotheses. |
| Lean/formal methods | A logical hull definition may only rename the desired object; what was actually proved? | Novelty | REPORT:26–41 states least-hull definition and the normalization fields; :43–50 states the composition. No priority claim. | Answered as scope; no literature novelty accepted. |
| Tree algorithms / rMAF | A normalized support with no leaf in a child is not yet a restriction/reindexing or DP charging theorem. | Correctness | REPORT:47 says “forbids assigning or charging”; :102–107 admits the required interfaces are open. The contradiction forms before the debt list. | MEDIUM: replace :47 with exact vertex absence and retain the charging debt beside it. |
| Tree algorithms / rMAF | Does this yield a new unrestricted algorithm or exponential bound? | Novelty | Opening REPORT:3–6 explicitly disclaims both; final interface list is specific. | Answered at the opening. No efficiency or novelty acceptance. |
| Discrete mathematics | The nonempty hypothesis of the hull equality is essential; empty root fragments could create a false charged block. | Correctness | REPORT:29–41 and :54–59 explain discard; FamilyGeometry:9 supplies HasLeaf. | Answered for normalization. Universal restricted-family construction remains open. |
| Discrete mathematics | Is the least-convex-hull fact itself claimed as a new mathematical result? | Novelty | REPORT describes a formal checkpoint and makes no historical claim. | Answered by absence of a priority claim; historical novelty not reviewed. |
| Executable verification | Does the address proof certify the graph hull extractor or Python implementation? | Correctness | REPORT:13–15, :30–32 and :100–107 explicitly keep those connections open. | Answered where the representation is introduced and in the debt list. |
| Executable verification | Are the three source descriptions independent certificates of the composition? | Novelty | REPORT:93–96 states that separately authored construction does not automatically verify the composition. | Answered; the fresh review is additional verification, not a new algorithmic claim. |
| User of the cost formula | Does “closing cost zero” mean closing a live singleton is free? | Correctness | REPORT:82–83 says zero, while the proved quantity is closedCost of an open family; cost Controls:75–78 adds a unit boundary charge. | MEDIUM: write “closed-region cost zero while open.” |
| User of the cost formula | Do counts here establish the objective of the executable optimizer? | Novelty | REPORT:102–107 leaves the representation and executable interfaces open. | Answered in body; opening already restricts the result to the finite address model. |
| General reader | Is the partial result accepted or still pending review? | Correctness | REPORT:4 says awaiting acceptance; :109 says “accepted partial target.” | LOW: synchronize status only after both fresh review records are complete. |
| General reader | What is the incremental contribution? | Novelty | REPORT:34–50 identifies normalization and root-path composition, with limits in the opening. | Answered as project progress; no publication novelty certification. |

The opening paragraph was reread last, without using the rest of the document.
It correctly says that the result is in the finite address-tree model and that
full G2, merging, executable interfaces, and a new exponential bound are not
established. Its pending-review wording must be updated together with the
closing status after parent adjudication, not retrospectively in this snapshot.
