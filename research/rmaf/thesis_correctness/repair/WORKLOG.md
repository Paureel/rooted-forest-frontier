# Root-safe normalization repair

## Target and status

Read REPAIR-TARGET.md first. The target is root-safe common-cherry normalization on valid active states, with original-edge provenance and exact existential coverage. Global correctness, runtime and convention transfer remain open. Prior sources, conditional proofs and receipts are preserved.

## Adversary-first controls

Pending: read the independent review; freeze the raw Cover witness, incompatible standalone normalization witness with compatible twin, and missing-root-parent fixture. Hunt valid active root-boundary states before constructing a proof.

## Distinct construction routes

Pending: component/partition route and original-edge exchange route, without cross-reading during construction. At most two active children, Astra xhigh.

## Exact theorem and consumer interfaces

Pending: finite-tree validity, active containment, AF compatibility, contraction/suppression and edge provenance requirements. Trace both exchanges in source Lemma 6.10 and the use in Theorem 6.12.

## Lean and independent review

Pending: kernel-check proved claims with explicit assumptions and axiom audit; stage fresh nonauthor review after construction. Finite testing remains separate.

## Result

OPEN. No repair theorem established yet.

## Review read: interface corrections

Read the independent review in full. Its universal raw-cutset Cover counterexample is an initial four-leaf state with a two-cut optimum outside A/BB/C. Source Lemma 6.8 gives existence of a covered optimum, so the old conditional Lean statements cannot be supplied with that universal interpretation. The review also gives a standalone normalization failure that violates active component containment, and a passing compatible twin. The 120 reviewed snapshots supplied no root-normalization premises. These are the frozen boundary tests for the repair; none is an algorithm-decision counterexample.

Raw Cover fixture opened: T1=rho→(a,(b,(c,d))), T2=rho→(((a,c),b),d), selected pair (c,d), pendant subtrees a,b. The review's cutset consists of the incoming edges of {a,c} and a; its forest blocks are {a},{c},{rho,b,d}. The declared optimum is two cuts and none of A, BB, C holds on that particular optimum. This fixture will reject any universal raw-cutset coverage reconstruction.

Normalization-domain fixture opened: T1=rho→((a,b),(c,d)), T2=rho→((a,c),(b,d)), F1={(a,c),b,d,rho}, E={ea,ec}, E2=∅. Replacing both path cuts by the LCA-parent edge makes {a,c} overlap {rho,b,d} in T1. The active containment hypothesis fails because F2 is connected while F1 is not. The matching-T1=T2 twin passes. Both cases must remain in the control set; accepting the bad fixture as a valid active-state proof would be an error.

Frozen repair controls in `controls.json` before new proof construction. The reviewed three-leaf missing-parent fixture is component-compatible because F1 is connected; it remains a structural fixture, not yet a trace of the exact algorithm. Separate counters will distinguish valid structural states, actually reached states, and nonvacuous root-normalization premises.

## Main-arm adversary: compound root fragment

Before proof construction, froze `compound-empty-hypothesis.json` and executed `compound_empty_adversary.py` using the earlier raw-deletion evaluator after its fixed controls. Result: active containment alone is insufficient if arbitrary E may cut inside compound sibling roots. T1=rho→(((a,(c1,c2)),x),y), T2=rho→((a,(c1,c2)),(x,y)), F1=T1 and F2=T2. With c=(c1,c2), E={ea,ec1,ec2}, E2=∅, the original cut forest is an AF, but removing ea reconnects a to the wrong upper restriction. The root component of c has become empty. E has three cuts while the optimum is one. This is a standalone/general-valid-state counterexample; atom-respecting and minimum-E variants survive it.

Receipt: `results/thesis-correctness-repair-compound-empty.json`. No existing source, conditional proof, or earlier receipt was changed. The result has not been shared with the two running distinct adversary routes.

Candidate narrowed premise to investigate: each endpoint root is connected in F2−E to a labelled descendant. This excludes the failed example while allowing internal cuts that leave a nonempty root fragment. A minimum-E theorem would additionally need a separate proof that an emptied common pendant root can be replaced by one parent cut and an intact matched component at lower cost. Neither claim is assumed.

## Existential consumers checked

Rebuilt the independent reviewer's unchanged ExistentialRepair.lean into this repair directory, then compiled ExistentialConsumers.lean. All three new consumer statements report no axioms: BCY existential selection, inherited exclusion conditional on an explicit graph lift, and A2BC existential selection with explicit inherited exclusion. These prove conditional logic only. Forest coverage, exchange, lifting and the global marked-state invariant remain open; no aggregate theorem count was changed. Compile logs and SHA256 provenance are retained in results/thesis-correctness-repair-existential.json.

## Independent adversary phase

The component route independently froze the same compound-empty mechanism using different upper labels; its four fixed controls and four corruption checks passed. The cutset is nonoptimal and reachability was not asserted. Its construction route is now authorized with explicit surviving labelled root fragments, and a separate investigation of whether minimum cutsets supply them. The edge route reports126 nonvacuous root-boundary normalization premises in actually reached five/six-leaf pilots, all nonoptimal E; its final receipt review remains pending. The routes have not cross-read each other's construction.

## Two-exchange cardinal accounting

Froze two-exchange-cost-spec.json and proved TwoExchangeCost.lean, retaining the actual second-path cut count instead of assuming it equals the earlier prefix count. Initial compile succeeded. The first author-check script run completed its exact controls and finite census but failed its overly strict expectation of an axiom-free omega proof: Lean reports exactly standard propext and Quot.sound. The script assertion was corrected to audit that actual list. This scalar substep did not execute controls before its first Lean construction; that protocol limitation is retained in its receipt, and fresh review must check the controls before reading the proof. No graph or AF preservation follows from this scalar theorem.

## Root-boundary adversary completed

Read the edge route's final report and summary. Its 2,000-input reached search retained 542 valid root snapshots and checked 12,170 normalization premises, including 5,584 with missing LCA parent and at least two path cuts. All 5,584 cutsets are nonoptimal. Separate structural enumeration tested 2,307 premises, including 597 root cases. No normalization failed in these atom-respecting finite checks. A complete actual cut/merge/finish trace and original-edge expansion witness are retained. Both distinct constructions are now running; neither has read the other's proof work.

## Reached-root cross-replay

The main arm imported the earlier raw-edge evaluator, without importing the edge route's checker, and replayed the complete frozen witness's graph data. Thirteen exact checks passed: before/after partitions, AF conditions against both source trees and active F1, absent parent, removed path cuts and cut-count drop. A corrupted result omitting the pendant cut was rejected. This is same-author cross-implementation evidence and does not replay the algorithm history; fresh nonauthor review remains pending. Receipt: results/thesis-correctness-repair-root-cross-replay.json.

## Cost-interface qualification

The source's equality between the actual second path-cut set and the earlier prefix set is not supplied merely by E⊆E0. The new inequality avoids needing that equality. No valid optimal forest instance falsifying the source equality has been constructed, so this is a removed proof obligation rather than a certified source counterexample. The scalar specification's phrase “unjustified equality” should be read in this limited sense.

## Review prepared

REVIEW-TARGET.md pins a fresh-code controls-first review and a source-level consumer audit. It will be dispatched only after both constructions have delivered, preserving their independence. The review must distinguish kernel-checked conditional logic and arithmetic from graph preservation and must leave global claims open.

## Formulation ladder and regime

The normalization domain is now a theory-finding task: distinct certified mechanisms defeat a missing containment premise, an undefined root-parent expression, and arbitrary compound-root restoration. FORMULATION-LEDGER.json records each dead form and its receipt instead of silently strengthening the target. The surviving-label feature comes from the certified compound-empty mechanism. This is a mechanism-driven candidate, not an exhaustive synthesis over theorem space. The two construction routes must still prove its sufficiency and trace actual consumers. Conditional existential branch logic remains a known-statement task.

## Distinct constructions delivered and review dispatched

The component route delivered a proposed restricted AF proof using rooted partitions and disjoint embeddings, an empty-common-subtree strict repair, and survivor propagation from original minimum E0 through the first exchange to the second compound pair(x,u). Its six local Lean lemmas do not formalize the AF argument. The edge route delivered26 scoped Lean lemmas for exact IDs, set/list costs, ranked parent paths, walks and conditional corridor isolation; none concludes AF preservation. It retained explicit shape/nonoverlap and source-edge translation obligations.

Read both construction reports and receipts. The graph hypotheses of the edge route match the stronger both-survivor component target, but their composition is not yet accepted. A fresh Astra xhigh reviewer was dispatched with a controls-first independent evaluator and a source-level interface trace. No author evaluator code may be reused by that reviewer. A new atomic partial-restoration witness from the edge route is nonoptimal and is a boundary control, not an algorithm counterexample.

## Direct two-stage original-edge boundary test

While fresh review runs, froze and executed two-stage-original-spec.json. In the common-uncle fixture T1=(((a,c),x),(b1,b2)), T2=((((a,b1),b2),c),x), the two optimal cutsets {ea,ec} and {ea,ex} each have size2. Adding pendant cuts and fully normalizing(a,c), then normalizing the original two-edge path(x,u), gives cut counts2→3→2 and the final pendant pair in both cases. Both intermediate/final forests passed the earlier raw-edge AF checker; deleting either final pendant cut failed. This uses one original graph throughout, avoiding any guessed edge ID after suppression in the executable witness. It does not establish a universal AF/suppression bridge. The old checker is reused and the evidence is author-generated, not a fresh-review result. The in-flight reviewer was not steered to this new construction.

## Version2 transport continuation

Pinned SECOND-EXCHANGE-TARGET.md after the direct two-stage controls. The candidate uses the specific2B geometry: pendant cuts suppress only the original a–c corridor; full first normalization leaves no cuts on that corridor. Every residual cut should therefore be an unchanged current edge with the same ID and endpoints. The second path is the original pair {ex,eu}; the optional incoming edge of their parent is also outside the affected corridor. A proof of this local transport could replace a general suppression theorem at this use site.

The edge agent resumed only in a new second_exchange_v2 directory with new receipts. It must execute an actual edge/endpoints-map adversary and a detached-rho root case before proving. The v1 constructions and fresh review remain frozen. This continuation has not been sent to the running reviewer; its eventual verdict cannot be claimed to cover the new version. Active child count remains two.

## Census denominator reconciliation

The reviewer reported44,862 N_anchor and42,204 both-survivor premises, while the author reported43,710 and41,052. Executed reconcile_census.py using the reviewer evaluator solely as a diagnostic, after its independent construction. Exact result: requiring every pendant incoming edge to be cut recovers the author's counts; permitting an E2 that empties a pendant subtree without cutting its incoming edge adds exactly1,152 premises to both counters. Yield removes that label-free side branch, so the broader E2 sibling premise still holds. A concrete witness is retained in results/thesis-correctness-repair-census-reconciliation.json. Both old receipts remain unchanged. The author census covers the direct-pendant-cut subclass of the stated n4 forest family; the fresh reviewer tested the broader E2 condition. Runtime2.04s. This diagnostic is not an additional independent verifier.

## First fresh review complete

Read review/REPORT.md and verdict.json. The reviewer accepts the restricted N_anchor normalization and strict empty-common-subtree repair as prose at their explicit finite current-forest scope. It rebuilt eight positive Lean files unchanged, rejected both false controls, and accounted for all41 printed axiom audits. Its fresh additional consumer census passed144 ordinary/swapped exchanges and136 two-stage minimum cases, including68 compound expansions and92 missing-second-parent cases. These finite checks are not universal proofs.

The reviewer independently supplied the corridor-specific second-exchange representation argument, but explicitly requested another independent read of that newly authored supplement. A second fresh Astra xhigh reviewer was dispatched from SECOND-REVIEW-TARGET.md, with fresh exact controls and an independent derivation before proof reports. Edge-route version2 continues separately and has not read reviewer feedback. The general optimal-completion/protected-origin lift remains the smallest unresolved general interface, followed by marked-state induction.

## Separate minimum-intactness candidate

The reviewed normalization and minimum-fragment arguments suggest a stronger local consequence: a global minimum cannot cut any internal edge of a common proper pendant subtree. Applying normalization with E2 empty to the two child subtrees at the parent of such an edge would strictly lower cost. Froze this candidate, executed its positive/negative controls, and checked all three/four-leaf connected input pairs with the earlier raw-edge oracle. No failure in159 nonvacuous common-subtree/minimum checks. The prose derivation and finite evidence are retained separately in MINIMUM-INTACTNESS-CANDIDATE.md; no fresh review or contraction theorem is claimed, and this candidate is not an input to the in-flight exchange review.

The common-subtree candidate checker was rerun after replacing an awkward output expression with the actual stored control optimum. Its unfrozen receipt now records the second run; first-run printed values are retained separately in thesis-correctness-repair-common-subtree-candidate-run1-console.json. Both runs have identical scientific counts and zero failures. No frozen target or earlier reviewed receipt changed.

## Second review and round result

Read the second fresh review report and verdict in full. It independently accepts N_anchor, strict empty-root repair, arbitrary-K two-pendant corridor transport, the conditional two-exchange minimum witness, and ordinary/swapped A2BC exchange as reviewed prose. It rebuilt eight original and four version 2 positive Lean modules unchanged, rejected three deliberately false controls, and found only standard axioms. The version 2 parent-graph encoding, derivation of splice witnesses and evaluator/graph correspondence remain formal obligations. No universal AF Lean theorem or global correctness result is claimed.

Its independent exact graph evaluator found no failures in 15,600 arbitrary-K cases and 16,384 pendant-internal cases. The four-leaf family supplied 44,862 anchor applications, 5,070 strict repairs and 9,897 minimum-fragment checks. Its five-label consumer family supplied 36 ordinary-c, 36 swapped-a and 38 two-stage minima. The four-leaf consumer count was zero. Version 2 reached-state evidence has zero absent-second-parent cases, so detached-rho controls remain separate structural evidence. These finite results do not establish universal conclusions.

Procedural qualifications retained: the second reviewer had controls and its independent derivation before proof reading but did not freeze the initial evaluator hash; final surviving-ID checks were strengthened afterward. Its bounded pendant-internal supplement lacked a separate measured pilot and took 5.21 seconds. The original scalar-control execution-order limitation and the first review's corrected partition-serialization issue remain recorded. Repository-wide bootloops-check was not run; no shared toolkit changed.

Created RESULT.md and version 2 summary without replacing version 1 or construction receipts. Updated the local dashboard to open, with the twice-reviewed local prose and scoped formal results distinguished from the general optimum/protected-origin lift, graph formalization, marked-state induction and full correctness/runtime obligations. The minimum-intactness candidate remains separate and unreviewed. No aggregate theorem count was changed.
