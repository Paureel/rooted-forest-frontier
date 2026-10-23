# Thesis protected-edge correctness reconstruction

Scope: Whidden (2013), Chapter 6, in the thesis rho-augmented convention, with q remaining cuts. Independent reconstruction; no complexity or convention-transfer claim.

## Checkpoint 0 — 2026-10-14

Read `/Users/paurel/Documents/ChatGPT/bootscience/research/rmaf/spec.json` before beginning. Next: read applicable protocols, source definitions and full Chapter 6; freeze exact state/branch semantics and planted controls before real-input search.

Open deliverables:
- Source read ledger and Theorem 6.12 dependency/use-site map.
- Faithful executable semantics, or explicit partial semantics that reject unimplemented obligations.
- Frozen positive and negative controls; independent exact reference and replay evidence.
- Meaningful kernel-checked local Lean theorem(s), with axiom audit.
- Precise smallest unresolved correctness obligation.

## Checkpoint 1 — source reconstruction

Read Whidden (2013), printed pp. 12–18 and 100–127 (PDF pp. 25–31 and 113–140). PDF pp. 121, 123 and 131 are image-only in the supplied extraction; inspected their retained PNGs visually. These supply Figures 6.1–6.4, the end of BCY, the full depth rule and G1/G2 runtime text. Source-reported facts, not verified conclusions:

- p.12: rho is a **labelled root with one child**, not an ordinary extra pendant leaf. The local reconstruction will represent that labelled root directly.
- pp.104–105: one active T1 component, matched completed components, and Rt is an antichain of equal pendant subtrees covering all remaining labels. Trivial moves finish a component or merge a common sibling pair.
- pp.106–107: cut requests are refused for protected edges and for a root edge whose sibling is protected; suppression inherits protection by OR.
- pp.107–111: branches AC, B, RB, RB*, 2B, BCY, A2BC, A3BC, in that priority (the pseudocode's SC is a naming inconsistency; the defined case is AC). A2BC has a separate protected-c form that cuts pendant edges first and then cuts a while protecting the pendant edges.
- pp.114–116: Theorem 6.12 chooses the leftmost promising path in a protection-free search, then argues this path avoids forbidden cuts. The written introduction-of-protection paragraph explicitly lists the cut-c forms but does not list A2BC's protected-c/cut-a form. This is a proof-interface obligation, not presently a counterexample to the algorithm.
- pp.101–103: Lemma 6.3 omits component containment from Lemma 2.4. Its immediate uses in Lemmas 6.4 and 6.5 compare against connected original T1, where containment is automatic. No algorithm-invalidity inference follows from its standalone overstatement.

Toolkit consultation: the 50-package index contains no rooted-forest exact combinatorial enumerator or Lean proof engine wrapper. The existing campaign oracle implementations and cwhidden sources are deliberately excluded to preserve a distinct reconstruction. New code here is problem-specific, retained with its controls and replay entry point rather than installed as a general toolkit instrument.

## Checkpoint 2 — controls and measured pilot

Frozen `controls.json` before first algorithm invocation. The four hand-constructed optima (identity, singleton boundary, one SPR triple, incompatible quartet) passed both the independent partition reference and the decision threshold. The comparator caught an intentionally wrong optimum; both input paths rejected duplicate labels and different label sets; negative budgets failed even on identity. Receipts: `results/thesis-correctness-controls-n4-limit0-seed612.json`.

Pilot: 30 uniformly sampled ordered pairs among the 225 four-leaf pairs, seed 612, completed in 0.021714291 s on this host. It exercised AC, B, RB, RB*, A2BC and refusal, but not 2B, BCY, A3BC or protected-c A2BC. This pilot measures the actual exhaustive-reference-plus-decision entry path. Extending to all 225 four-leaf pairs is projected below one second assuming the measured same-size per-pair distribution; the five-leaf regime gets a separate pilot. Real progress is the number of completed exact pair comparisons written in the receipt. All finite outcomes remain TESTED, not universal correctness certification.

Provenance: `reference.py` was authored here from the leaf-partition definition, uses recursively pruned rooted restrictions and address-set intersections, and never imports `algorithm.py`. `algorithm.py` uses integer-node forests, cuts, suppression and protection, and never imports the reference. Shared layers are Python and the input trees; feared branch-selection/cut-protection errors live only in the latter route. Authorship is shared, so this is algorithmic independence, not a fresh-author verification. No earlier campaign oracle, runtime-agent code, or cwhidden implementation was read. Values touched by debugging will be marked development data, never independent certification.

Five-leaf pilot: 60 sampled ordered pairs, seed 612, completed in 0.087317 s. It added A3BC and 2B coverage without mismatches. Projected full 11,025-pair sweep: approximately 16.0 s under the measured same-size mean; decision budgets are -1 through optimum+1. Launching this bounded sweep. BCY and protected-c A2BC remain separate coverage debts until an actual trace reaches them.

## Checkpoint 3 — complete five-leaf sweep and local Lean lemmas

All 11,025 ordered five-leaf pairs matched the independently authored partition oracle for every budget -1 through optimum+1, in 16.511981916 s. This reaches the source proof's omitted A2BC protected-c branch 80 times. No mismatch or SemanticHole occurred. This is finite testing of a reconstruction with declared interpretive choices, not a theorem about every input.

Six-leaf pilot (100 sampled ordered pairs, seed 612) passed in 0.337171125 s and reached all eight named branches, plus the separate protected-c A2BC form. It includes 2 BCY and 3 protected-c events. Extending to 3,000 uniformly sampled six-leaf pairs is projected approximately 10.1 s under the measured same-size distribution. The next receipt will retain one concrete trace per branch to expose its coverage witnesses.

`ProtectedBranch.lean` now kernel-checks six local theorems: ordinary A2BC, protected-c A2BC, A3BC protection, BCY protected-uncle omission, OR protection provenance, and associativity of OR inheritance under path concatenation. The first four are explicitly conditional on coverage/exchange/inherited exclusion; they do not establish those graph hypotheses. The last two prove the concrete Boolean data invariant. No sorry, custom axioms or native_decide are used. Initial compilation failed because `protected` is a Lean keyword; retained the failure log, renamed the variable, and compiled again successfully.

## Checkpoint 4 — local adversary and source counterexample

The 3,000-pair six-leaf sweep passed in 10.1432225 s. The receipt now retains concrete input/trace witnesses for every named branch, including BCY and protected-c A2BC.

Added `local_obligations.py`, a distinct original-edge cut enumerator. It obtains candidate states from the reconstruction but does not use its cut, suppression, parent or shape routines to decide agreement. It enumerates deleted original edges, connected label components, and minimal rooted restrictions. The four frozen hand controls passed this third route too. Its first four-state pilot checked both endpoint versions of the two-pendant exchange in 0.027402 s. The next bounded run requests up to 80 distinct states from the saved branch-witness corpus; same-source maximum cost projection is approximately 0.55 s, while source-state complexity variation remains explicit.

A direct two-label counterexample to standalone Lemma 6.3 was executed: F1 has isolated labelled rho and a, while F2 joins rho to a. There are no triples and no two target components to overlap, but cuts cannot connect the F1 components. The receipt records this alongside the consumer ruling: connected T1 in 6.4 and 6.5 excludes this witness. The original lemma's overstatement has not been promoted into an algorithm-failure claim.

## Checkpoint 5 — reproducibility and expanded exchange tests

The first branch-witness corpus supplied only 8 distinct two-pendant states (16 endpoint checks). This was a bounded corpus, not 80 completed states. Expanded collection with seeded six-leaf inputs (seed 6312, budgets 0–3) to fill an 80-state cap. The original-edge enumerator then passed 160 endpoint checks in 0.210607709 s. `history/local-obligations-v1.py` preserves the smaller collector. These observations are development checks; a fresh author must still reproduce the graph lemmas.

Made endpoint/tie ordering deterministic by sorting atom labels before comparison. `history/algorithm-v1.py` preserves the exact source hash of the earlier sweep receipts. This changes only source-permitted arbitrary ties; rerunning all four/five-leaf pairs and a fresh six-leaf sample with seed 613 will check the revised reconstruction. Earlier results remain in their original receipts.

The source title-page check corrected this note's abbreviated title to *Efficient Computation and Application of Maximum Agreement Forests*. `source-read-ledger.json` records the source hash, actual full ranges read and image-only page inspections. Chapter 3 proof imports have not been rederived by this arm and remain explicitly conditional.

## Checkpoint 6 — current result and remaining proof

Deterministic version (seed 613 receipts): all 225 four-leaf pairs, all 11,025 five-leaf pairs, and 3,000 six-leaf sampled pairs matched, for 14,250 comparisons of the current version. The six-leaf receipt includes 90 BCY and 136 protected-c events. Earlier arbitrary-tie receipts remain available with their preserved v1 code.

Seven Lean theorems now compile. Added `normalization_cost_le`, the exact cost inequality after adding ≤1 missing pendant, removing ≥1 path cut, and restoring ≤1 parent edge only when ≥2 path cuts were removed. The false control `0 + 1 - 0 + 0 ≤ 0` was rejected by Lean with exit status 1; the error explicitly states that `decide` proved the proposition false. `NegativeControl.lean` is intentionally outside production builds.

Executed a separate root-domain witness for Lemma 6.5, with three ordinary leaves. The lemma's E/E2 premises hold, the LCA lacks a parent edge, and omitting the nonexistent edge yields an AF by direct-deletion verification. Smallest local obligation: prove the root-safe common-cherry path normalization, retaining original-edge provenance, then derive both endpoint pendant exchanges using the checked cardinality inequality. Global closure still needs all branch coverage, contraction/finish, graph transport and termination proofs.

Prose/number review: checked title-page identity, page offsets, numerical denominators, theorem counts, and the difference between finite comparison and universal proof. Inspected PDF p.118 visually to verify that the e_b terms in Lemmas 6.6 and 6.8 are printed source inconsistencies, not extraction errors. Two wording passes removed an abbreviated source title and clarified that the first local run had only eight distinct states. This remains an internal reconstruction for fresh-author review, not a publication-ready proof.
