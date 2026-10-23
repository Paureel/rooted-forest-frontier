# Review questions

Fresh nonauthor review is pending. This author checklist does not satisfy the fresh-context requirement in referee-sim or prove-protocol. It identifies the interfaces and scope statements that the reviewer should test.

| Audience | Objection | Axis | Answer location | Severity / state |
|---|---|---|---|---|
| Rooted-MAF theorist | Does restriction preserve actual vertex disjointness after unary suppression, including an LCA below the original root? | Correctness | RESULT paragraph 4; Embedding.literal_clear_transport; fixed lower_lca control | Fresh review pending |
| Rooted-MAF theorist | Is a new mathematical result being claimed without comparing prior work? | Novelty | RESULT opening explicitly makes no novelty claim | No novelty claim |
| Lean reviewer | Are desired conclusions supplied as fields, or proved for the literal original checker? | Correctness | Forward.forward_decomposition; Reconstruction.reverse_reconstruction; all input hypotheses printed in source | Fresh review pending |
| Lean reviewer | What has been added beyond the frozen geometry results? | Novelty | RESULT paragraphs 2–4 describe local restriction transport, checker decomposition, and reconstruction; no priority claim | Fresh review pending |
| Algorithm integrator | Can I use the forward theorem when Q's shapes disagree, and what extra data does reverse require? | Correctness | RESULT paragraphs 2–3 give the distinct hypotheses and exact original family | Fresh interface trace pending |
| Algorithm integrator | Does the result establish the full faster algorithm? | Novelty/scope | RESULT opening preserves all three OPEN milestones and excludes full algorithm correctness | Explicit scope |
| Reproducer | Could an unrelated module or custom axiom evade a namespace-only audit? | Correctness | replay.py audits all local-origin declarations and resolves every module path; hostile PlantModel leg rejected | Executed author evidence; independent replay pending |
| Reproducer | Do finite fixtures establish the universal result? | Novelty/scope | Universal proofs and fixed fixtures have separate paragraphs and separate Lean declarations | Fresh review pending |

Author prose checks covered source locators, counts, status qualifications, and the absence of novelty/full-algorithm claims, followed by a second sentence-level read. A fresh reader must still review the final prose and the proof interface.
