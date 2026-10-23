# Fresh scope and prose review

Initial report SHA-256: `0cdef4a957443cf97a7cf82565bbb3d170b0478b393a24f612f98c4d3f10026c`.
Revised report SHA-256: `b5d3be61c586ecbf49424c8f97469f2b58f02316775051bf84f88d85428d08d2`.
This fresh-context pass applied referee-sim, prose-lint, and reading-contract.
It found one low-severity terminology issue, corrected by the parent reviewer
and checked again here. No substantive scope or number defect was found in the
material inspected. No unresolved finding remains from this bounded pass.

## Finding

**Resolved LOW — name the queried Lean definition accurately (prose-lint N3/N11).**
The initial `REPORT.md:29` said “30 theorem queries and the `normalize` constructor query.”
The declaration at `source/FamilyTrim.lean:50` is
`noncomputable def normalize (F : RawFamily t k) : RawFamily t k where`.
It is a definition of a normalization function; calling it a constructor can
be read as the Lean declaration category. The revised sentence reads
“30 theorem queries and one query for the definition `normalize`.” I checked
the changed paragraph against the declaration. The count 31 remains correct;
the receipt's existing field name remains historical metadata.

## Referee table

The audiences below follow from the formal proof method, the tree-family
model, the finite controls, and the potential use of the result in an RMAF
implementation. Objections are interpretive review judgments; source facts
supporting the judgments are identified in the answer column.

| Audience | Axis | Strongest standard objection | Answer at the reader's point of concern | Severity / action |
|---|---|---|---|---|
| Lean and formal verification readers | Correctness | A kernel check can certify a circular specification or a theorem about the wrong object. | The opening restricts the result to the finite address model. Rows 1, 3, and 8 of the semantic table distinguish admissible input fields from the constructed normal form. `FamilyModel.lean:144–156` and `FamilyTrim.lean:50–92,164–174` support that distinction. | No substantive finding. Definition-name correction verified. |
| Lean and formal verification readers | Novelty | Rechecking the author's proof is not an independent derivation or a new formal theorem. | `REPORT.md:97–100` expressly identifies the shared kernel and proof sources; lines 47–52 separately identify the three reviewer statements. Lines 88–89 make no novelty claim. | No finding; no literature priority assessed. |
| Tree and graph theorists | Correctness | An intersection-defined hull need not have been connected to graph paths, and counting indexed regions is not automatically a finite-set-cardinality theorem. | The opening excludes graph correspondence. Semantic rows 3 and 6 distinguish proved hull properties, the explicit `k + indicator` definition, and the missing finite-set-cardinality equivalence. `FamilyModel.lean:85–99` and `FamilyTrim.lean:125–132` agree with this description. | No finding. |
| Tree and graph theorists | Novelty | A normalization lemma may be a routine consequence of hull monotonicity and disjointness; a checked proof alone cannot establish a mathematical advance. | The title identifies a review. The report's final mathematical scope statement at lines 88–89 explicitly withholds novelty. No comparison to prior graph results is claimed. | No finding; novelty remains unassessed. |
| RMAF and dynamic-programming researchers, including incumbent-method users | Correctness | Whole-family normalization does not prove restriction, assembly, correct closure charges, state decoding, or solver correctness. | The opening excludes these broader connections. Lines 79–89 list the remaining transition, charge, decoding, and refinement obligations. The pinned `INTERFACE.md` also leaves these obligations separate. | No finding. |
| RMAF and dynamic-programming researchers, including incumbent-method users | Novelty | A generic recurrence theorem plus normalization cannot establish a new exponential base or improvement over existing solvers. | Lines 88–89 explicitly withhold a new exponential base and novelty claim; the opening promises only normalization. | No finding; incumbent literature and performance were not evaluated. |
| Reproducibility and test reviewers | Correctness | Registered regressions and a failed module can look like broad testing when the failure was merely an import error. | Lines 12–22 name the finite registered rows and exclude a holdout census. Lines 35–45 give the proposition failure and matching clean twin. The fresh Lean receipt records `actual 0 = 1 rejected by decide` and `0 = 0 accepted by decide`. | No finding within receipt review; no new execution performed. |
| Reproducibility and test reviewers | Novelty | A separate implementation can share its specification and fixtures, so agreement cannot establish a new result independently. | Lines 93–100 disclose shared specifications and fixtures and distinguish finite semantic checks from the same-source kernel replay. | No finding. |
| Practitioners and general readers | Correctness | “Acceptable” might be mistaken for permission to rely on unrestricted RMAF or Python output. | The opening immediately limits acceptance to the address model and excludes Python refinement. The closing scope paragraph repeats the concrete outstanding obligations. | No finding. |
| Practitioners and general readers | Novelty | A positive review might be mistaken for evidence of a faster or novel algorithm. | The report claims neither performance improvement nor priority; lines 88–89 explicitly exclude both implications. | No finding. |

## Numbers, prose, and opening

The retained direct-control receipt lists 17 passing row records. The frozen
controls contain 14 rows and the amendment adds 3. The `raw-empty-open` record
supports closed cost 2, labelled-block count 2, and support-object count falling
from 3 to 2; the report distinguishes those units at lines 16–17. The family
receipt lists 11 model queries, 16 trim queries, and 4 control queries: 31 in
total, including the definition `normalize`. The dependency audit lists 19 and
8 queries separately. The supplement receipt lists 3 reviewer theorems.
These are readings of retained records, not calculations or builds performed
by this sub-reviewer.

The parse/composition read, honesty pass, number pass, targeted vocabulary
sweep, and separate colleague-style read found no further actionable defect.
The scopes attached to the control counts and proof provenance convey distinct
limitations and should remain. “Must preserve” at lines 81–82 states an
obligation for future transition proofs, rather than claiming those proofs
exist. The opening was read again last, as the report's abstract: its concrete
limitations prevent acceptance from implying full G2, executable correctness,
or a novelty result.

## Inspection limits

Read: `REPORT.md`; the four pinned family source files `FamilyModel.lean`,
`FamilyTrim.lean`, `FamilyControls.lean`, and `NegativeFamily.lean`;
`INTERFACE.md`; `controls.json`; `controls-amendment-v2.json`; and the four
`results/triple-family-fresh*.json` records. The report hash was checked
directly. The source syntax and receipts support the bounded judgments above.

The separate path and cost routes were not read. This pass did not rerun
controls or Lean, inspect the reviewer lemmas' source, verify historical
read order, audit old receipt hashes, assess literature novelty, or run a
larger census. Build outcomes and the three supplementary lemma counts were
read from the fresh receipts. This was a Markdown text review; no separate
rendered-document visual check is claimed. The terminology revision received
a follow-up read and introduced no further finding.
