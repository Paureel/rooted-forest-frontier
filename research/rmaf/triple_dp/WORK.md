# Triple-component completion route

Status: OPEN. Specification read first on 2026-10-14. This route studies exact polynomial completion when every incompatible source component is a triple. No improved unrestricted exponential bound or safe cover is claimed. Whidden (2013) prior art remains unresolved.

## Immediate plan

1. Read the prior note as unverified mathematical source and the applicable scientific protocols.
2. Freeze independent small-instance positive, malformed-input, and wrong-result controls before search.
3. Attack the target-tree connected-region characterization, including source disjointness and adjacent same-color region failures.
4. Build an exact terminal dynamic program and independently compare against a small exhaustive oracle.
5. Formalize precise connected-region/DP lemmas in Lean 4.35.0 using Std; record shared semantics and open graph correspondence.
6. Account for state, transition, and witness costs; identify reachable baseline children only when justified.

## Current debts

Initial checkpoint: all mathematical claims, code checks, and Lean proofs were pending. Later checkpoints below record executed evidence. Existing partition/span code would be secondary evidence only, if used. This route has not read the pure-bridge route work.

## Source reading and method choice

Read the full 279-line `sources/previous-work/RESEARCH.md`; its Section 6 is the unverified retrieved candidate, not an instruction. The exact load-bearing sentence is: “A partition is a valid refinement exactly when its target embeddings are vertex-disjoint, every block is monochromatic, and no block contains all three leaves of a bad color.” Section 6 also states at most six active states per bad color and allows same-color adjacent regions to remain separate. Sections 8–10 explicitly retain the safe-cover and prior-art debts. No claim of independent discovery of that recurrence is made.

Read the six requested skills and BootLoops tools index. The nearest local `oracle/README.md` describes partition/span enumeration, but the required independent check cannot reuse that lineage. Therefore this route uses a new graph edge-deletion enumerator and a separately authored scalar DP. These are problem-specific instruments, registered here rather than general toolkit additions. No existing oracle implementation has been read or imported. Shared layers are raw nested-tree input, Python standard library, and this author's interpretation of the mathematical definition; fresh-author verification remains necessary.

`controls.json` is frozen before either implementation is executed. Expected values are hand constructions: singleton and full-good nulls; a conflicting triple needs exactly two blocks; two crossing source pairs need three blocks; two pendant bad triples need four. Deliberate malformed inputs, an optimum shifted by one, and a topology-compatible but overlapping forest must all be rejected. The edge-cut oracle will enumerate target partitions and source cut forests independently of the DP. Finite survival is discovery evidence only.

## Adversary-first checks and timing

2026-10-14: frozen controls executed before census: 13/13 passed or caught (five hand optima, five malformed instances, wrong-result comparison, overlapping wrong witness, false same-color-merge claim). Initial receipt retained as `results/triple-dp-controls-initial.json`; a receipt-path typo was corrected before census. No mathematical code was changed after comparisons.

Pilot: `./bootloops-python research/rmaf/triple_dp/check.py census --n 5 --limit 200` completed 200 comparisons in 0.03128 seconds (plus 0.008 seconds controls). This early slice includes startup cache creation, so only a conservative sub-minute allowance is used for the n=5 full census, not a calibrated cross-size forecast. Progress unit is fully checked cases, including optimum equality, witness membership, and partition-by-partition characterization equality. Any mismatch aborts immediately.

Full n=5 census completed: 9,660/9,660 generated completion instances, no optimum, witness, or characterization mismatch; 1.20287 seconds. This independently reproduces the source note's reported count for this family, but remains authored discovery evidence. Six-leaf fixed two-triple pilot: 100 comparisons in 0.10933 seconds. With 945 target trees and 3×3 source topologies, the full family has 8,505 instances; the pilot projects about 9.3 seconds under the same per-case cost. Allow 60 seconds, with measured checkpoints retained.

## Lean checkpoint

`./bootloops-python research/rmaf/triple_dp/audit_lean.py` returned `{"status": "passed", "theorem_count": 22, "negative_control": "caught"}`. Lean version is 4.35.0. Core imports Std; only the finite SemanticControls file imports the existing RMAF model. The first generic theorem build passed. A subsequent exact mask-join proof failed because Lean could not synthesize a decision procedure for an unrestricted existential; explicit constructor simplification fixed that local proof. Failed and successful logs are retained. Accepted axiom inventories contain only propext, Classical.choice, Quot.sound, or none. The deliberately false claim that a bad triple has one region fails as required.

## Scale and baseline checks

The replayable `large_checks.py` passes five positive witness-checker controls and catches an overlapping witness, then checks n=60 and n=600 output witnesses. These are **not optimality checks**. For n=600,m=200,b=134, the DP records 1,044,329 value entries, 1,563,989 candidate transitions, 1,043,458 child-closing evaluations, and exactly 1,199 reconstruction visits. Runtime observed on the replay: 0.21080 seconds solver and 0.01194 seconds graph witness check, including the solver's polynomial validation; these are not comparative benchmark claims.

Read baseline v2 text PDF pp.17–18 (Rule 4) and p.24 (Rule 7 and Figure 16). The post-hoc quartet example in `results/triple-dp-baseline-child.json` is an actual Rule-4 a-cut child, with one paid cut and one remaining cut, final component optimum three. This illustrates a legitimate detection site, not safe pre-cutting or improved worst-case recurrence.

The detailed handwritten proof and formal debts are in `PROOF.md`. Acceptance remains OPEN. A separate fresh-author verifier is building a partition/triple/path enumerator without reading the author implementation first.

## Stronger local Lean checkpoint

The follow-up adds arbitrary distinct-label proper-partition agreement across the three representative rooted shapes, exact full-triple agreement iff the representative shape matches, and structural classification of one-, two-, and three-leaf binary trees. The new audit returns 28 accepted theorem axiom inventories with the false-cost control still caught. Formal sibling-swap/relabeling transport and G1–G3 remain OPEN. No generic full-MAF theorem is inferred from these local facts.

## Validation scope and prose pass

The final Lean audit rebuilds the shared RMAF source into this route’s `.deps` directory before checking SemanticControls; it does not modify upstream proof sources or compiled outputs. The general BootLoops package suite was not rerun by this route because no toolkit package was changed and its global result output lies outside route ownership; the parent was notified to report the workspace suite separately. All route checks and their negative controls executed through workspace wrappers.

Applied the prose-lint honesty/number pass to PROOF.md and README.md, then a separate sentence/paragraph read. Replaced a normalized source quotation with a paraphrase tied to the baseline locator, and made the reconstruction bound explicitly count label references, with string serialization separate. A vocabulary sweep found only the literal ordinal “the first region”; no novelty claim is attached to it. A fresh report-scope reader is running under the independent verifier.

## Mixed-component adversary

After the first proof draft identified source-span transfer as G1, froze `mixed-plan.json` for a post-hoc n=7 supplement: 25 sampled target trees, a target-compatible four-leaf component, and both incompatible topologies of the complementary triple (50 cases). This is a targeted adversary rather than held-out acceptance. The four-case pilot took 0.07517 seconds; scaling the same distribution gives about 0.94 seconds for all 50, with a conservative one-minute allowance. Each case compares the optimum, reconstructed witness, and every characterization partition. No production solver change is involved.

## Reachable overlapping-triple child

Constructed a nine-leaf source/target pair whose target cherry {a,b} has three nonempty source pendant subtrees, two of which are incompatible triples after cutting. All target and source cherry path counts are at least two, so Whidden(t=1) and common-cherry tidying do not preempt the t≥3 rule. The retained plan is `reachable_child.py`; its path counter has three hand controls before the constructed instance. This example tests a legal Whidden(t=3) all-pendant-cut child with overlapping bad triples. A hand argument predicts three further cuts; the script demands exact agreement and does not claim the original uncut pair's optimum.

Compute allowance: n=7 mixed comparisons completed about 102,400 distinct target-edge masks in 1.047 seconds. The new n=9 target and source each have 65,536 masks, with 17 vertices rather than 13, so a conservative same-engine allowance of 10 seconds is used. This is a small finite post-hoc example, not an unmeasured large search.

The mixed supplement completed 50/50 cases in 1.04662 seconds. The nine-leaf reachable child completed with three paid and three additional cuts, final seven components. A follow-up added all nine cross-color pair-span intersection checks, establishing the stated finite lower-bound obstruction; it passed in 1.40077 seconds together with the exact cut oracle and witness. No original uncut nine-leaf optimum was claimed and no production solver changed.

## Fresh replication and final scope review

The fresh-author partition/rooted-triple/direct-path oracle passed 10,029 cases and 70,660 partitions for n≤5, followed by 8,505 cases and 212,625 partitions on fixed two-triple n=6 inputs. The latter includes 3,780 cases with two bad triples. Its separate positive, malformed, wrong-result, mutant, and clean-twin controls passed or were caught. This is independent reference-code replication on overlapping input domains, not new-input holdout evidence. The verifier repaired its receipt location without changing the original receipt bytes; the migration manifest records those hashes.

The fresh verifier recompiled and audited the 19 core Lean theorems. The route-author audit separately covers 28 total theorem inventories: those 19 plus nine semantic theorems sharing RMAF.lean. The fresh scope review found no HIGH issue and three MEDIUM clarifications, now fixed in PROOF.md: distinguish live and full component counts after tidying; require cost-preserving soundness/completeness up to trimming rather than a raw-support bijection; distinguish 28 author-route audits from 19 fresh-core audits. Its review retains the original document hash and an exact many-to-one trimming example. A second self-read checked the revised opening, counts, lemma statements, and conclusion. G1–G3 and the executable-to-graph interface remain OPEN; no safe cover, unrestricted recurrence improvement, or novelty acceptance is reported.

## Single-region formal continuation

Continued G2 with `ConnectedRegions.lean`, defining exact address-path membership from LCA and prefixes. Lean proves that a root-containing region is path convex iff it is prefix closed; this yields both directions of its root/child decomposition, including the condition that each occupied child restriction contains its own root. The file also proves that the gapped support {[], [false,false]} is LCA closed but not path convex. This resolves a single-region assembly step, not the disjoint-family, label-trimming, or cost correspondence.

The first positive build completed in 0.24 seconds. The separate audit rebuilds the core dependency and checks eight new axiom inventories plus the 19 already-counted core ones. Its initial destructive control failed for missing reducible-instance synthesis rather than falsity; that failed log is retained. Expanding the proposition in the control made it fail for the intended false proposition, and the complete audit passed in 1.40 seconds. The new eight statements bring the distinct author-route total to 36, while preserving the original 28 receipt. A fresh verifier was asked to replay only this supplement; no fresh replay is assumed before its receipt returns.

Fresh replay returned PASS for all eight new statements, 19 rebuilt dependency audits, the intentionally false omitted-vertex control, and a passing clean twin; 1.44 seconds. Its scope review confirms that the theorem is an exact single-region address decomposition, with finite-tree/labelled-family/cost correspondence still open. The gapped input came from the verifier's earlier report and is correctly marked shared evidence. This gives 27 distinct freshly replayed support statements, with the nine RMAF semantic statements still route-author-only. Because the fresh receipt used the direct version-pinned Lean launcher, a separate wrapper replay was requested to satisfy the workspace execution-recording convention while preserving the first receipt.

The wrapper replay passed in 1.54 seconds through `bootloops-lean` with workspace `ELAN_HOME`. Its comparison receipt confirms unchanged source bytes, clean control, and axiom reports, and preservation of the earlier receipt/logs. The wrapper receipt is `results/triple-dp-verification-connected-wrapper.json`. Final status remains CONDITIONAL, with exact G1–G3 debts and the unchanged nonterminal recurrence written in PROOF.md.
