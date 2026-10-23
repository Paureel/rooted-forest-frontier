# GLOBAL-Q independent route journal

Started 2026-10-14. Route owner: global_quotient_prover. Scope is this directory and result prefix `algorithm-balanced-cover-quotient-`.

## Frozen objective and status

Read `research/rmaf/algorithm/SAFE-COVER-TARGET.md` before this file was written. Exact goal: total source-cut generator in size/time O*((5/4)^b), preserving at least one original optimum, every output pure-bridge or compatible/triple, pure-bridge original unmarked tau <= b/2. Licensed alternate: alpha=3/2, theta=1/2, subject to the full paid construction and strict runtime product bound. Algorithm, Correctness, Smaller base remain OPEN.

## Independence boundary

Do not read parent journal, joint_macro or paid_cover code/proofs, or X0 implementation. Parent reports X0 independently executed all nine controls with no pin mismatch; receipt may be read as evidence. Source pure-bridge G1-G7/triple G1-G3 are conditional imports, not proved Lean graph implementations. No descendants will be spawned.

## Route GLOBAL-Q

Investigate weighted/global separators on the quotient of unknown optimum source regions and constrained certificate enumeration without an optimum oracle. Source-cut accounting and one-original-optimum survival are separate obligations.

## Named obligations

- Q1: define a computable certificate language with only original counted source cuts.
- Q2: a global balanced separator of unknown optimum regions exists with a charged bound.
- Q3: enumerate a surviving certificate within licensed alpha^b without an optimum oracle.
- Q4: all emitted forests satisfy completion-class conditions and unmarked local tau bound.
- Q5: connect generation, paid completion, reconstruction and decision-budget iteration.
- Q6: retain independent numerical/Lean evidence, falsification witnesses and axiom audit.

## Activity and evidence

- Immediate skeleton recorded after the target read. No construction claim made.

## Failed proposals and exact witnesses

None yet.

## Proved constituents

None yet.

## Remaining lemma

Entire constructive chain Q1-Q5 is open.

### Read record and admissible method (2026-10-14)

Read SPEC.md and FROZEN-CONTROLS.json; also prove-protocol, reading-contract, independence-bookkeeping, planted-truth, timing-discipline, tool-stewardship, acceptance-gate, bootloops/tools/README.md, relevant capability search in toolkit/ours/{README,RECIPES}.md and external/TOOLS.md, and gatekeeper/GUIDE.md. Gatekeeper provides numeric oracle/heldout hygiene, not finite rooted-tree graph/cut enumeration; no indexed package provides the required graph instrument. Any new finite instrument here is problem-specific and intentionally independent of X0 and production code.

Preserved source `research/rmaf/sources/previous-work/RESEARCH.md` read at lines15-136,156-199,203-262. Load-bearing quotation (§8 lines237-239): "If the original pair has optimum at most b cuts, at least one original optimum refines some F_j." and "Every F_j is a pure-bridge completion instance, or belongs to the polynomial triple class." Source marks its statement a research target at line232. Quotient balancing alone does not establish the second quotation.

X0 receipt path resolved to `research/rmaf/results/algorithm-balanced-cover-x0-controls.json`; receipt read, X0 implementation not read. Shared frozen input/spec is allowed; no X0 code dependencies are used. This receipt is only the reported preconstruction control gate. Our own search output will be development data, burned for route tuning, never independent certification.

### Q2 preliminary constituent and obstruction sites

For an optimum edge-cut set K and any C subset K, full K-components refine C-components: deletion removes paths, so no original optimum component is split across precut components. Residual edges are K\\C, and each C-component contains at most |K\\C| such edges. Choosing |C|=ceil(|K|/2) therefore bounds each original unmarked local cut distance by floor(|K|/2), conditional only on explicit original optimum-cut/partition correspondence. This establishes an existential budget localization route, not an executable generator. It says nothing yet about pure-bridge degree geometry or the triple terminal class.

The quotient tree may have high degree even when the source is binary: a connected optimum region can expose arbitrarily many boundary cuts. Therefore a one-edge centroid separator assertion is suspect; a star quotient is the first falsification target. The larger obstacle is paid oracle-free enumeration of subsets of unknown K: enumerating arbitrary source edges is n^ceil(b/2), not O*(alpha^b). No generation base claimed.

### Measured small-witness search

Pilot `smallest_probe.py pilot` completed all 225 four-leaf pairs in 0.015663375000258384 s, plus all pairs on1-3 labels. The generator reproduced fixed rooted tree counts1,1,3,15. Before the five-leaf run, projection: (0.015663375/225) *11025 *(93/22) *(9/7) = about4.2 s, under conservative candidate-count and linear support-size scaling. This is a conditional projection, not a scientific claim. Stop at the first three-cut pair or after all11025 five-leaf pairs. No larger census is planned.

### Executed evidence and method revision

X0 literal receipt summary (read, not rerun or used as implementation): `finished_rows=9`, `expected_fixture_count=9`, `mismatches=[]`, `verdict=REPRODUCES-ALL-FROZEN-CONTROLS`. Receipt provenance is X0's own declared fresh source enumeration; this route does not independently certify it.

Own pre-search control/output summary, quoted verbatim from `algorithm-balanced-cover-quotient-probe.log`:

```json
{"controls_passed": 4, "corruptions_caught": 3, "opt": 3, "candidate_star_is_optimum": true, "Q2_ONE_refuted": true, "pilot_seconds": 0.0019032079999306006, "output": "/Users/paurel/Documents/ChatGPT/bootscience/research/rmaf/results/algorithm-balanced-cover-quotient-probe.json"}
```

Q2-ONE is rejected. Exact six-leaf witness: S=(((((a,b),c),d),e),f), T=((a,c),((b,e),(d,f))), Opt=3. K isolates b,d,f and contracts to a3-spoke star. Every singleton C subset K has residual quotient counts2,0 and original unmarked tau2, exceeding floor(3/2)=1. This kills a one-edge separator for every optimum quotient, not the existence of safe-cover generators. K is one original optimum; other optima were not excluded. Full source edges, supports and exact cut-set counts are retained in the receipt.

The quotient budget b=3 is structurally smallest: b≤2 gives a path quotient, with a balancing one-edge split. A pilot-first complete development census on ≤5 leaves, including all11025 five-leaf pairs, found no Opt≥3. Full result `algorithm-balanced-cover-quotient-smallest-five.json`, measured2.985534040999937 s. Thus the six-leaf witness is the smallest leaf count supported by this exact same-author census. Independent oracle certification remains pending. No larger census run.

Repair output, verbatim:

```json
{"repairs_checked": 3, "all_pure": true, "tau": 1, "paid_pre_cuts": 2, "total": 3}
```

Q-HALF-ANY is also rejected. Exact seven-leaf witness: S=(((c,(a,b)),d),((e,f),g)), T=((a,(((e,(c,d)),f),g)), Opt=2. K cuts A={a,b} and C={e,f,g}. C alone leaves the incompatible four-leaf block {a,b,c,d} with d=1 and impure target overlap degrees2/3. Both pure-bridge and compatible/triple fail, while tau meets half-budget. A alone gives a pure balanced forest, explicitly preserving the existential alternative. Ordinary binary scope only; no unspecified reduction history asserted. Geometry positive/corruption controls preceded this test.

Geometry output, verbatim:

```json
{"opt": 2, "K_is_original_optimum": true, "Q_HALF_ANY_refuted": true, "existential_some_half_subset_terminal": true, "pilot_seconds": 0.0010326669998903526}
```

After two failed formulations, the theory-finding question is recorded: can polynomially checked global geometry conditions select a small family of balanced original-cut certificates without selecting a hidden optimum? Method revision GLOBAL-Q-GUARDED replaces one-edge and arbitrary-half selection with explicit terminal-geometry and local-witness certificates. The strengthened certificate language asks local witnesses on all outputs; this is sufficient for the target and avoids ambiguity when the terminal classes overlap, but is not claimed necessary.

### Kernel constituents and arithmetic control

`EdgeLocalization.lean` executed successfully on Lean4.35.0. Actual graph theorem `original_optimum_refines_precut` has no axioms. `residual_reach_exact` uses only propext, Classical.choice, Quot.sound. Half-residual and paid-component arithmetic also passed. All accepted theorem axiom audits omit sorryAx; no custom unproved axioms/native_decide are used.

An initial arithmetic draft attempted unavailable mathlib tactics. Its failed source is retained as `EdgeLocalization.failed-arithmetic-v1.txt`, with pilot errors retained. A rational-equality sqrt pilot would have had a vacuous Rat hypothesis s*s=2; it was not accepted. The final source instead proves unconditional rational upper-bound comparisons and the nonvacuous hypothesis s*s≤2, with7/5 as a kernel-checked witness. Real ordered-field radical transfer remains a prose arithmetic implication, separate from Lean graph/executable claims.

`FalseStar.lean` executed and failed: `Tactic decide proved that ... 3 - 1 ≤ 3 / 2 ... is false`. `FalseExponent.lean` failed reduction on the false rational comparison rather than giving an explicit false-value diagnostic. Consequently `NegativeArithmetic.lean` separately proves the negation of that comparison with kernel decision, together with the failed/repaired star twins; its successful axiom audit is retained. No false-control compile failure is counted as a successful production proof.

### Total constructive fallback and full charge

`SlowCover.py` enumerates all actual source cut sets with ≤b cuts, rejecting empty pieces and accepting only complete agreement forests. It emits original edges, full original component vertices, exact labels/restrictions, target supports, r paid precuts and0 residual cost. No optimum oracle or local solver is called. The generator is total in the algorithmic model; all outputs are compatible with local d=0. The source-support extension argument in RESULT.md proves every original optimum partition has a cut realization among these candidates, with exactly |P|-1 nonredundant cuts. Decision budgets0,...,n-1 terminate and reconstruct input labels directly without reductions.

Charged size/time is polynomial(n)*sum_{i≤min(b,n-1)} binomial(2n-2,i), including failed candidates and output serialization. It is an explicitly unlicensed fallback, not a smaller-base result. Output, verbatim:

```json
{"controls_passed": 4, "corruptions_caught": 4, "seconds": 0.001406041999871377}
```

Four input controls passed; the crossing case has all six distinct optimal partitions; four incorrect-total twins were rejected. Fallback and witnesses share this route's primitives and are development records, not independent verification.

### Remaining theorem and statuses

Q1: explicit original-edge certificate language implemented in the slow fallback; guarded efficient language described.
Q2: cut-subset refinement is kernel-checked; local residual localization has a prose proof plus executed finite witnesses; one-edge and arbitrary-half terminal proposals refuted.
Q3: OPEN. Enumerate a globally guarded surviving family in total size/time O*((3/2)^b) (or exact(5/4)^b), including construction of all local witnesses and rejected recognition candidates, without an optimum oracle.
Q4: OPEN for an efficient universal generator. Exact geometry tests and witnesses retained; local budget alone does not imply terminal class.
Q5: total, explicitly slow exhaustive decision/optimization implementation supplied; full requested faster-algorithm chain remains OPEN. Conditional source G1-G7/triple G1-G3 imports are unchanged.
Q6: kernel constituents and proposition-level false controls executed. Fresh nonauthor source-model review, oracle reconstruction, code replay and use-site trace still pending.

Algorithm, Correctness, Smaller base remain OPEN under the target acceptance rules. No novelty claim made. Parent, paid_cover, joint_macro and X0 implementation were not read, and no descendants were spawned. New instruments are deliberately problem-specific; their meaning and acceptance limits are described in RESULT.md. No upstream source, pin or frozen receipt was modified.

### Draft review preparation

RESULT.md received two author passes: first source/count/scope consistency (including removal of an incorrect "independently" label for shared-oracle local recalculation), then sentence/paragraph and terminology review with prose-lint. The final learned-case counts and timings were checked against retained JSON receipts. This is an author review only. `referee_sim_RESULT.md` lists correctness/novelty objections per audience, explicitly awaiting a fresh reviewer; it does not claim the fresh-context referee-sim requirement has been met.

`progress.json` and `algorithm-balanced-cover-quotient-status.json` retain the open milestones, independent-review requests and current file pins. The parent received the handoff and can integrate the route-local card without this agent editing outside its owned directory. The later kernel corruption-control theorem `refinement_without_cut_subset_is_false` executed with no axioms; it proves the subset hypothesis cannot be dropped. Accepted logs audit12 statements across the two production Lean files. A final lexical sweep found no sorry/admit/custom axiom/native_decide in these production files, and no sorryAx in their successful axiom logs.
