# Review of reader objections

The reviewer did not author the target SEMANTICS.md or its proof files. This table applies the referee-sim skill to that target, not to the reviewer's own prose.

| Audience | Standard objection | Axis | Answered where | Severity | Required disposition |
|---|---|---|---|---|---|
| Algorithm theorist | Does the checked local logic imply the theorem for every valid forest state? | Correctness | Target says graph proofs remain open, but universal raw `Cover` cannot hold for all Opt cutsets | High | Use existential coverage or justify a normalized family; review includes a concrete witness and a conditional Lean repair |
| Algorithm theorist | Does this establish a new exponential bound? | Novelty | Target explicitly makes no running-time or novelty claim | Low | Preserve scope |
| Formal proof reader | Are there custom axioms, sorry proofs or missing imports hidden behind the successful compile? | Correctness | Isolated replay and per-theorem axiom output | Low | Seven original lemmas and true/false controls replayed successfully at their stated scope |
| Formal proof reader | Are these new graph theorems? | Novelty | Target describes local Boolean/cardinality/optimal-family logic | Low | Call them local conditional results; source graph imports remain open |
| Source specialist | Are defects in a standalone lemma being presented as counterexamples to the intended algorithm? | Correctness | Target already separates the root-domain issue; review adds containment-domain witness and use-site analysis | Medium | Carry active-state compatibility explicitly; preserve the distinction in the summary |
| Source specialist | Is a retrieved source theorem being presented as a new result? | Novelty | Source attribution and no novelty claim are explicit | Low | Preserve attribution; no external literature conclusion added |
| Implementer | Did the adversarial test exercise the protected-c and BCY cases and detect bad answers? | Correctness | Fresh replay reaches both cases; frozen wrong-answer controls fire | Low | Finite 534-pair check reported, universal correctness open |
| Implementer | Does this replace a certified MAF implementation or provide a new runtime guarantee? | Novelty | Target calls it a tested reconstruction and excludes runtime claims | Low | Preserve scope |

The target's opening scope is appropriately limited. Its logical interface still needs the quantifier correction before a universal proof can instantiate it. The review summary places that finding before the finite-test counts.
