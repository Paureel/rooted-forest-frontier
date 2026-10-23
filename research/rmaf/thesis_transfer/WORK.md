# Whidden thesis transfer audit

Status: OPEN. Fresh verifier task started 2026-10-14.

Scope: reconstruct ordinary rooted MAF without rho (k components) versus Whidden's rho-augmented MAF/rooted SPR parameter. No novelty or improved-base claim is accepted yet.

Independence: before reading any previous oracle implementation, freeze hand controls and implement a distinct exact partition-and-span oracle. Existing formal definitions may be inspected only after independent controls.

Stages:
1. Read toolkit and skills; freeze controls; pilot independent semantic attacks.
2. Read source locators and actual Chapter 2/6 text, inspect corrupt formulas in PDF.
3. State and prove the exact transfer theorem and solution mapping.
4. Formalize feasible interface; audit source load-bearing obligations.

Owned paths: research/rmaf/thesis_transfer/, results/thesis-transfer*, progress/thesis-transfer.json.

## Initial provenance and capability decision

Read spec.json before work, then toolkit index and scientific skills. Toolkit graph packages (cosmoflow, dogtag, geotriage) concern Feynman graphs and do not enumerate rooted labelled-tree agreement partitions; no existing general MAF instrument appears in the index. A deliberately independent, one-task exact enumerator is therefore justified. No existing oracle code or formal definitions have been opened. The shared semantic input is only the campaign definition and hand-derived controls. controls.json was written before code or scan outputs.

Pilot plan: controls first, then all pairs at n=3 and n=4 with same exhaustive partition engine. Record elapsed seconds per completed pair. Any larger n requires new measurement because Bell-number and tree-count growth invalidate linear extrapolation across n.

## Stage 1 independent results

Fresh controls passed: 5/5 hand optima; 7/7 malformed rejects. Corrupting the opposite-ancestry rho optimum from 3 to 2 causes AssertionError (exit1, retained log). Exhaustive n3/4 scans cover 126 unordered tree pairs, 1107 ordinary forests and 2772 augmented forests. The 12 gap-one n4 pairs refute equality of ordinary and augmented optima. Forced rho-singleton add/erase maps passed for every tested forest. These finite checks are evidence only, not a universal theorem.

## Prospective black-box transfer (pinned before tests)

A stronger reduction avoids requiring arbitrary forest-input initialization in the thesis: add two fresh leaves in opposite caterpillar order, U1=(beta,(alpha,T1)), U2=(alpha,(beta,T2)), then add rho in the thesis convention. Candidate K_rho(U1,U2)=K(T1,T2)+1; thus thesis cut parameter q equals original component parameter K exactly. See gadget-spec.json. This is an independently proposed reduction during source audit; it is not a retrieved thesis claim. Adversarial tests precede proof.

## Timing checkpoint before n5

Original augmentation n4 pilot: 0.0079s profile construction + 0.0048s for 120 pairs. Gadget n4 pilot: 0.3372s profile construction + 0.0614s for 120 pairs. For gadget n5 the profile workload grows by (105/15)*(Bell(8)/Bell(7)) = 33.0 times, and per-case graph work grows with vertex count; pair count grows 46.4 times, with more feasible partitions. Projection is only a bounded planning approximation, not a measured n5 rate: around tens of seconds. Run n5 as a new timed pilot with output units = profiles and pair/forest checks; terminate/replan if it exceeds 60 seconds without completion. No n6 run planned.

After independent controls and both corruption controls passed, read shared RMAF.lean semantic definitions. New Lean results may import this shared Boolean definition layer; their evidential independence is reduced at that layer. Python oracle continues to use BFS paths and explicit numbered vertices with no RMAF or previous oracle imports.

## Completed first transfer stage

The exact opposite-caterpillar reduction has a complete authored mathematical proof in TRANSFER-PROOF.md, graded provisional pending fresh independent verification and the protocol's diversity requirement. Its successful finite attack covers 5,693 unordered input pairs across n=1,…,5, with 93,720 ordinary-forest lifts and 1,143,020 augmented-forest erase maps. The n5 pilot completed in 19.1059s, of which 12.8016s built profiles. No n6 scan was launched because this stage's mathematical issue is now specified and larger scans would not replace proof.

Lean 4.35.0 replay rebuilt the shared RMAF source and checked 11 declarations in Transfer.lean, with only propext, Classical.choice and Quot.sound among recorded axioms. The actual structural lemmas concern restriction disagreement and span/root intersections. The generic minimum-shift theorem explicitly assumes the semantic maps. Full AF transport and unary-rho/sister-leaf equivalence remain unformalized. The first draft had simplifier failures, retained in lean-pilot.log; no result was accepted from that build. The repaired clean build and same-order false-theorem rejection are retained under lean-audit/ and results/thesis-transfer-lean.json.

Three distinct corruption controls were caught: wrong rho optimum; same-order gadget; false same-order Lean theorem. Disabling vertex disjointness also admits the frozen crossing-pairs witness, demonstrating that control's sensitivity. Seven malformed inputs were rejected.

Source work read Chapter2 and all Chapter6, then the relevant Chapter3 proof chain. Official institutional title-page metadata and source formulas were checked. SOURCE-AUDIT.md maps the imported lemmas and source theorem hypotheses. A visually confirmed scope counterexample to the standalone arbitrary-forest wording of Lemma6.3 is retained, with its tree-reference uses explicitly distinguished. This does not refute the thesis algorithm. The smallest next reconstruction obligation concerns A2BC's already-protected-endpoint branch and provenance of protected edges through suppression; the depth/P,Q cost invariant remains separate.

No official toolkit code or integrity pins changed. Toolkit-wide selftests were not rerun because no toolkit behavior changed; this folder's exact controls, negative controls, and Lean replay were executed instead. External full texts referenced by the thesis as [22], [23], [101], [102] remain unread. A fresh Astra xhigh reviewer is performing the required framing/prose review; that bounded review does not replace a fresh exact universal-proof verifier.

## Framing review and edits

Fresh Astra xhigh reviewer found no mathematical gap in the written gadget proof, while explicitly declining solver, universal Lean, or novelty certification. Adopted the four recommendations: opening now gives ordinary-AF and rho-model scope; encoding correspondence states the exact vertex replacement; n is defined as |X| beside the runtime; witness output is conditional on exposing its cut forest within the stated bound. The unsupported pure-decision self-reduction aside was removed. The second fresh review resolved all three medium framing findings and found no new substantive issue. Its remaining cosmetic base-2 wording edit was applied. This bounded semantic review is not the protocol’s fresh-code verify pass, so provisional status remains.
