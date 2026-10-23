# Scope review

The audiences are formal-methods reviewers, tree/phylogenetics researchers,
algorithm analysts, and users of the Python solver. Each uses a different
standard of correctness, and each could misread a normalization result as a
complete solver proof. The opening of `REPORT.md` limits acceptance to the
raw-to-retained finite-address normalization theorem and names the missing
interfaces.

| Audience | Standard objection | Axis | Answer location | Severity and action |
|---|---|---|---|---|
| Formal methods | The hypotheses may contain the normalization theorem, or admitted axioms may certify it vacuously. | Correctness | Semantic audit rows 1 and 8; executed checks and exact false diagnostic. | No unresolved finding after inspection and isolated rebuild. |
| Formal methods | Counting new theorem names may inflate the amount of new mathematics. | Novelty | Executed checks distinguish 30 theorem queries, one definition query, and 27 dependency queries; opening limits the mathematical contribution to normalization. | No novelty claim is made; the report does not equate declarations with discoveries. |
| Tree and phylogenetics researchers | An abstract address closure need not be the minimal subtree used by the agreement-forest problem; a formal count may only name `k`. | Correctness | Opening; hull and block-count rows; remaining interfaces. | The report explicitly states the absent executable/graph and finite-cardinality translations. Acceptance is limited accordingly. |
| Tree and phylogenetics researchers | Trimming connected regions to their labelled spans is a standard observation, not a new structural result. | Novelty | Remaining interfaces, final sentence. | No scientific novelty claim is made or reviewed. A novelty claim would need a separate literature review. |
| Algorithm analysts | Preservation of an index count does not prove the four transitions or their closing tolls sound and complete. | Correctness | Opening and remaining interfaces, second paragraph. | Full G2 remains open; no transition theorem is credited. |
| Algorithm analysts | A new normalization lemma does not imply an improved running-time base. | Novelty | Remaining interfaces, final paragraph. | No improved-base claim is made. |
| Python solver users | Compiling Lean and passing small graph controls does not verify Python tables or reconstructed witnesses. | Correctness | Opening, executed-checks paragraph 1, remaining interfaces paragraph 3. | No Python correctness claim is made. |
| Python solver users | An independently written tiny checker is not a new solver or a performance advance. | Novelty | Provenance and reproduction; the direct-checker scope. | The checker is described as a one-shot review instrument, with no performance claim. |

The cold opening-only pass found the essential scope limitations in the first
paragraph. The count wording was checked against the executed receipts, and
the semantic table explicitly distinguishes author statements from reviewer
interpretations and supplementary lemmas. The review uses a fresh context
that did not author the normalization modules; the report itself was also
read in a separate prose pass for claim strength and count units.
