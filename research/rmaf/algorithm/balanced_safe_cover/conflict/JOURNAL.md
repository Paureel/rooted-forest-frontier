# GLOBAL-C journal

Route opened: 2026-10-14. Lens: global incompatibility packing, separator certificates, and constrained enumeration of original source cutsets. No optimum oracle may enter the proposed algorithm.

## Frozen target

Read `../../SAFE-COVER-TARGET.md` before construction. Seek a sparse family of at most b nonredundant original source precuts, preserving at least one original optimum and meeting pure-bridge or compatible/triple recognition, with original unmarked local distance at most b/2. Exact target generation time and count: O*((5/4)^b). Licensed alternative: alpha=3/2, theta=1/2, c=1+sqrt(2), only after all costs and interfaces are proved.

## Independence boundary

Do not read `quotient/`, parent workfiles/code/proofs, `joint_macro/`, `paid_cover/`, or the X0 implementation. Use frozen X0 receipts as external evidence only. This route does not implement local multi-color splitting cores.

## Controls and construction status

- [ ] Read applicable protocol skills and toolkit guides.
- [ ] Inspect frozen X0 receipts.
- [ ] Freeze GLOBAL-C fixtures and corrupted controls before running.
- [ ] Measure pilot before any larger census.
- [ ] Derive universal constituents or exact obstruction.
- [ ] Pay generation, recognition, and completion costs.
- [ ] Audit any Lean constituents and false controls.

## Results ledger

2026-10-14: read X0 `algorithm-balanced-cover-x0-controls-v3.json`: 9/9 frozen fixtures reproduce; no mismatches. Read equal-halfbudget-n4 receipt: the n=4 equal-halves source split has tau=0, both terminal predicates true, original optimum=1, no surviving optimum, and charged total=2. This refutes that particular separator rule, not safe-cover existence.

2026-10-14: GLOBAL-C spec and literal controls frozen in `SPEC.md` and `controls-v1.json` before code execution. Toolkit indexes contain no relevant exact finite-tree instrument; Gatekeeper guide read and found outside this combinatorial scope. Wrote a one-shot stdlib enumerator, with source-cut-mask and leaf-partition methods. They share tree primitives and an author, so their comparison is an internal differential test, not fresh nonauthor verification.

Executed frozen controls, output `research/rmaf/results/algorithm-balanced-cover-conflict-controls-v1.json`:

```text
"verdict": "FINITE-CONTROLS-REPRODUCE"
"fixtures_passed": 7
"comparisons_passed": 20
"mutation_catches": 23
```

No expectation was edited after execution. Both equal-half witness and its safe singleton-cut twin reproduce. The frozen quartet packing-gap fixture has optimum=2 and maximum disjoint conflict packing=1, rejecting packing tightness (C3) while leaving C1/C2 open. Finite tests will be labeled finite. A failed candidate will not be reported as nonexistence of the target cover.

2026-10-15 pilot: `algorithm-balanced-cover-conflict-pilot-n4-v1.json` exhausts 236 ordered pairs through n=4 and 14,549 cutsets with no C1 mismatch. All n<=3 pairs have tight packing; 30/225 n=4 pairs have packing=1 and optimum=2, making four leaves the smallest tested gap (also every smaller labeled topology was enumerated).

Runtime planning: initial n5 head-only pilot took 0.399s/100 pairs but had only one source topology, so it was not used for extrapolation. Revised randomized pilot (`pilot-n5-v2.json`, fixed seed 20261015+n) samples 200 ordered n5 pairs in 0.840s, final 150-pair window used for the projection. Same machine, same exact checks, uniform shuffled pair distribution. Assuming steady per-pair cost at fixed n=5, 11,025 pairs project to under 60s. This is below the long-run threshold; full n<=5 census is licensed. Progress unit: completed pair and checked cutset counts in the emitted size rows; CPU/exit status is not acceptance.

Lean compilation initially failed only in two positive-control proofs, due unbounded existential decidability. Preserved source as `ConflictPacking-pre-control-fix-v1.lean` and failure log. Replaced those proof steps with explicit witnesses and arithmetic. Production compiles with only standard propext/Classical.choice/Quot.sound axioms; no sorryAx, custom axiom, or native_decide. FalsePackingControl fails because `decide` proves the false singleton transversal proposition false. The packing lower bound and saturated-optimal certificate are source-neutral; C1's tree semantics remain outside Lean.

2026-10-15: full n<=5 census completed: 11,261 ordered pairs, 2,836,949 source cutsets, no characterization mismatch. Measured n5 runtime 45.360s vs 46.194s projection. There are 7,770 n5 packing gaps, all packing=1/optimum=2. The current complete receipt is `algorithm-balanced-cover-conflict-census-n5-v1.json`.

C4 versioned in `SPEC-v2.md`: global original-edge column inclusion safely preserves some optimum. Generic substitution and list-length theorems compile. Four abstract controls, nine corruption catches, and 236 n<=4 exact source-pair comparisons pass. The first M>2opt witness has M=5,opt=2; this rejects a simple candidate-universe cardinality shortcut, not sparse-cover existence.

C5 preregistered in `packing-ratio-target-v1.json`: hypothesized optimum<=2*maximum packing. The first constructed six-leaf test fires: S=((a,(b,c)),(d,(e,f))), T=((a,d),((b,e),(c,f))), optimum=3,packing=1, all1,024 source cutsets checked. Retain `algorithm-balanced-cover-conflict-packing-ratio-n6-v1.json`. This second packing bound is rejected; continue using packing only as a lower bound.

C6 v3 formulation follows the C5 failure, so temporal provenance is explicit. For matched mixed-cherry sectors, handwritten optimum=m and a safe root split lead to a one-output polynomial special cover. Pilot m=2,3 (`mixed-cherry-pilot-v1.json`) reproduces four Q cases,20 comparisons,21 corruption catches including the m1 excluded case. Three m3 cases take0.074128s (~0.024709s/case). For m4, source cutsets grow1,024->16,384 and Bell partitions203->4,140; conservatively scale by the larger ratio20.394, giving under0.51s/case and under8s for15 Q cases, assuming this fixed-family scale. This is below the long-run threshold; now launch m4 finite checks. Progress unit is completed Q cases and their exact cutset comparisons. No m>=5 census is launched.

C6 finite checks finished:19 Q cases throughm4,248,896 sourcecutsets,95 exact expected comparisons,96 corruption catches. Complete m4 took8.706s, slightly above the under8s projection because the larger tree and post-row precut/geometry calculations also cost time; still comfortably below the long-run threshold. The script's per-row `seconds` stops before the optional precut calculations, so use the full stage walltime for planning.

Implemented `matched_sector_solver.py` with original unsuppressed edge receipts and explicit partitions. It recognizes the special input geometry, structurally certifies tau=0, rejects budgets belowm, and builds an m-cut optimum without calling partition/cut/distance/packing optimization oracles. It shares Tree and agreement-checking primitives with the finite instrument; this is declared shared lineage. Solver regression:38 budget decisions across19 Q cases plus2 exception/outside-family controls pass. All completion and validation is polynomial for this restricted family.

Prose integrity passes: checked numbers against receipts, corrected the inaccurate suggestion that removing hyperedge supersets could change maximum packing count, clarified all scope statements, and reread the edited proof. Fresh nonauthor source-model/interface and referee simulation remain required; no descendants were spawned under the parent instruction. The unrestricted sparse generation theorem remains open.

## Open obligations

1. A source-model theorem connecting conflicts, unsuppressed embeddings, and necessary source cuts.
2. A global separator selection rule whose branches retain at least one optimum.
3. A size/time bound including recognition, local distance certification, and all completion queries.
4. Imported pure-bridge and triple-terminal correctness and executable correspondence.
5. Original-label reconstruction and total algorithm proof.
