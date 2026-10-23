# Fresh nonauthor normalization review

Started 2026-10-14. Scope: local rooted-MAF normalization repair only; no global algorithm, runtime, transfer, or novelty certification.

## Sequence and independent controls
- Read REVIEW-TARGET.md first.
- Created this skeleton before supporting reads.
- Fresh evaluator and frozen controls: pending.
- Planted corruptions: pending.

## Primary-source read ledger
Pending direct reads of thesis pages 12–18, 101–103, 112–116.

## Construction audit
- Component route: not yet read.
- Original-edge route: not yet read.
- Consumer/interface pass: pending.
- Lean compile, axiom audit, false control: pending.

## Findings and exact scope
Pending. No correctness verdict yet.

## Remaining obligations
Pending.

### Evaluator design and provenance, before construction reads
The toolkit index was consulted by exact graph/tree and validation capability. It has no rooted agreement-forest evaluator; its phylogenetic package is likelihood-oriented. A one-shot standard-library evaluator is justified by the required disjoint lineage. No author, component, edge, or earlier review implementation has been opened or imported. Shared inputs are only the three frozen JSON specifications. The independently implemented representation uses original tree vertices, leaf-labelled minimal hulls, canonical rooted restrictions, and pairwise hull disjointness. Initial source-model assumptions are tested by the frozen controls and will subsequently be checked against the primary source. A bounded fixture pilot is run before any census. Exact failure criterion: any Boolean, integer, or block mismatch fails; output corruptions must be rejected.
First fixture run stopped on raw-cover block-list ordering: computed {a},{b,d,rho},{c} equals frozen {a},{c},{rho,b,d} as a partition. Corrected only serialization comparison to set-of-frozensets; no mathematical output changed. This is logged as fixture-contact debugging, not independent discovery of expected values.

Fresh controls completed before construction reads. Executed `./bootloops-python research/rmaf/thesis_correctness/repair/review/fresh_exact.py`; receipt `results/thesis-correctness-repair-review-controls.json`:
```
{"status": "passed", "forest_controls": 5, "scalar_controls": 5, "corruptions_caught": ["AF-output", "optimum-output", "partition-output", "scalar-output", "root-parent-output"], "elapsed_seconds": 0.0018608749996928964}
```
Exact raw optimum 2, cutset outside A/BB/C and covered alternative; containment-invalid bad normalization and valid twin; absent-root-parent valid normalization; compound empty root fragment: AF true→false, cut count 3, optimum 1. Five scalar values are 2,3,2,2,3; negative controls violate hypotheses 3 and 8 respectively. Fixture pilot is complete and no long-run estimate is needed.

### Component construction first read
Read component_route/PROOF.md §§1–7 after successful controls. It explicitly proposes full-path restoration, adds `N_anchor` (or two surviving endpoint-root fragments), proves empty common proper subtree replacement by a partition argument, and leaves exact edge translation for the second (x,u) exchange open. Preliminary audit: the strict local saving uses at least two internal cuts and at most one incoming insertion; a constrained completion optimum is insufficient. The prose carefully distinguishes this from the Lean local binary/counting lemmas. Exact source and finite adversarial checks remain pending. No construction verdict yet.

### Original-edge construction first read
Read edge_route/CONSTRUCTION.md after controls. It claims 26 scoped Lean theorems about original-ID membership, count, walks, confinement and ranked parent maps; it explicitly leaves both labelled restriction isomorphism and nonoverlap open. Its partial-restoration example has atomic endpoints but a nonminimum E, so the reported scope is correctly narrower than refuting the minimum-cutset consumers. Replay and Lean/source audit remain pending. The route explicitly requires graph-derived corridor boundaries, anchor-walk avoidance and suppression transport.

### Primary source read: definitions
Opened retained Whidden 2013 source text, printed pp.12–18 (PDF pp.25–31); its first page confirms author/title/July 2013, not a newly verified bibliographic entry. Page12 explicitly augments a binary leaf-labelled tree with a unary labelled rho root and defines induced trees by suppressing unlabelled nodes with fewer than two children. Page15 defines F~E, AF of current forests and minimum cut count. Page16 allows compound endpoint roots via equality of entire descendant subtrees. Page17 Lemma2.2 supplies the component-containment bridge to original-tree AFs. Page18 Lemma2.4 supplies containment, nonoverlap and triple compatibility. The fresh evaluator's unary-rho, minimal hull and rooted restriction conventions agree with these definitions. The retained TXT has explicit PDF-page markers, not form feeds; an initial form-feed extraction failed and was replaced by marker extraction, with no source-content inference from the failed command.

### Primary source read: normalization
Opened printed pp.101–103 (PDF pp.114–116). Lemma6.5 p102 defines E1 as **all** E path(a,c) edges. Its one-cut argument explicitly asserts the existence of a leaf x′ in the endpoint subtrees connected to u after E; this is exactly the unsupported step hit by the compound-empty control. The displayed two-or-more-cut formula includes eu without a stated absent-parent exception. The corrected formula must handle that boundary. Page101 Lemma6.4 supplies cut-superset AF preservation, but it does not imply that partial restoration contains the full normalization when the full operation adds eu. Exact quote ledger will be attached to the report.

### Primary source read: consumers
Opened printed pp.112–116 (PDF pp.125–129). On p112 E0 is explicitly of size e(T1,T2,F2), although it extends a selected prefix E; this is a global current-forest optimum, not just minimum under forced prefix cuts. On p113 E3 is taken from E, whereas Lemma6.5's E1 is taken from all of E0. The text's equality E′1=E1 is likewise not justified merely by E⊆E0. The second endpoint u is the reconstructed common a/c subtree and can be compound. On p116 the source restores ec alone; applying the all-path lemma requires an extra argument. The source proof on pp115–116 explicitly follows the C branch for newly protected edges; no endpoint-swapped protected-c case is written there. Protection inheritance and equivalence of cutting root siblings are invoked in the global path argument, beyond local normalization.

### Fresh adversary pilot and partial-restoration replay
The 500-AF-cutset n=4 pilot ran in 0.0564 s; 890 N_anchor premises, 756 two-survivor premises, 186 empty-subtree repairs, 59 minimum-survival checks, no failure. The full n=4 workload is bounded by 225 tree pairs × 3 rho-boundary states × 256 cut masks; even a coarse proportional projection is seconds to tens of seconds, not hours. Proceeding with the bounded complete family. This family covers whole trees and rho-detached forests, not all yielded active forests.
The frozen atomic partial-restoration witness reproduced: original AF true, partial AF false, full AF true, E size 2, optimum 1. It is in-regime for an arbitrary-E replacement claim and out-of-regime for a minimum-E consumer. Script/receipt: review/hunt.py and results/thesis-correctness-repair-review-hunt-pilot.json.

### Fresh complete n=4 family result
Executed hunt.py to completion in 3.463 s. All 225 ordered four-leaf binary tree pairs, the three compatible whole/rho-detached states, and all available-edge cut masks were enumerated. Receipt: 51,516 AF cutsets; 44,862 N_anchor premises; 42,204 two-survivor premises; 7,152 compound two-survivor premises; 4,710 absent-parent two-survivor premises with >=2 path cuts; 5,070 empty-subtree repairs; 9,897 minimum-survival checks; zero failures. These counts use this fresh evaluator's explicit denominator and are not intended to match another route's differently counted premises. This remains finite evidence.

### Lean statements read: component, scalar, existential
EmptyRoot.lean proves six local cut-decorated-binary-tree/counting theorems, including the lower bound two and strict cost improvement, without AF predicates. TwoExchangeCost.lean proves the frozen natural-number inequality. ExistentialConsumers.lean explicitly assumes graph coverage, exchange, inherited exclusion and protected-origin lift. Its three theorems cannot discharge those premises. Next: original-edge sources, local rebuilds, axiom and false-control audits.

### Source display and rebuild checks
Rendered and visually read printed pp.102,113,116. The PDF confirms the formula scopes and prefix/all-cut distinction found in the TXT; in particular p113 displays E′1=E1 and p116 restores ec alone. PNGs are retained in review/source-pages/.
All eight positive Lean source files rebuilt into review/lean-build/ without changing source hashes. Both original-edge phantom-parent and empty-root three-cut false controls returned errors, as required. Every printed axiom dependency was empty or a subset of {propext, Quot.sound, Classical.choice}. No delivered source contains sorry, admit, custom axiom, or native_decide after comments are stripped. Receipt: results/thesis-correctness-repair-review-lean.json.
The original-edge two-stage fixture and three intact compound endpoint expansions passed for both frozen starting optima (four cases total). After the first exchange u and x both retained labelled root fragments; the second path was exactly {ex,eu}; the final cuts were {eb1,eb2}. Deleting either required final cut failed AF in all four cases (eight negative instances). This is finite evidence for the direct-original-edge idea and does not prove suppression transport.

### Final classification and acceptance pass
The local component N_anchor theorem and strict empty-common-subtree repair are reviewed at their exact model/hypotheses. The edge route's 26 named local statements are reviewed at their actual Lean scope. Full forest normalization is not kernel formalized. The raw Cover, compound-anchor and partial-restoration failures are preserved as executed, machine-readable reproductions with their regime limits. The global repair remains open at exact optimal-completion/protected-origin lifting and marked-state composition.
A corridor-specific second-exchange representation was independently reconstructed in LOCAL-RECONSTRUCTION.md. This reviewer-authored supplement is marked for a further independent read; it is not promoted to a multi-pass complete source proof. The completed consumer census recorded 144 ordinary/swapped exchanges and 136 two-stage minimum cases (68 compound, 92 absent-second-parent), with no failure.
Applied the acceptance-gate structure to exact arithmetic: no fit, approximation, digit claim, precision escalation or leave-one-out applies; frozen exact comparisons, independent author lineage, executed negative controls and retained scripts supply the applicable checks. Applied prose-lint meaning/number/provenance and separate plain-language passes to REPORT.md; source quotations stay unchanged. No global or universal theorem is inferred from finite no-fire counts.
