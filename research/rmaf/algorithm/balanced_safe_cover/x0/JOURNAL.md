# X0 independent adversary journal

## Mandate and separation

2026-10-14. Fresh independent rooted-MAF evaluator and frozen-control audit for balanced safe-cover. Target read first: `../../SAFE-COVER-TARGET.md`. No parent journal, unfinished joint_macro, or paid_cover code/proofs will be read. Scope: `x0/` artifacts and independent result receipts. No proof construction; exact finite witnesses only.

## Frozen inputs

Pending read of FROZEN-CONTROLS.json. Expected fixtures will be treated as pins, with mismatches reported without revision.

## Model and implementation lineage

Pending source-model reading. Evaluator will be written from the mathematical model with no oracle code reuse. Exact partitions, rooted induced topology, unsuppressed source/target vertex supports, and independent distinct source precut realizations will be recorded.

## Runtime plan

Pending toolkit and timing-discipline consultation, then pilot before broader census.

## Executed controls

None yet.

## Counterexample search

Pending frozen controls. A failed arbitrary splitting strategy does not refute existence of the safe-cover target.

## Verdict and limitations

Open.

## Read/model ledger (before code)

Read `sources/previous-work/RESEARCH.md`, definitions lines 15–31: "T[B]" is the unsuppressed minimal spanning subtree; rooted restriction suppresses unary vertices; agreement partitions require rooted topology and vertex disjointness in both embeddings; no implicit rho or acyclicity. Read pure geometry lines 33–37: purity requires degree exactly two in both embeddings at every overlap vertex. Read triple class lines 156–166: each source component agrees, or has exactly three labels. Read target lines 1–68 and frozen controls v1 in full. The target is explicitly an existence target, and automatic arbitrary-cut survival is not licensed.

Toolkit consultation: `bootloops/tools/README.md` has no general rooted-MAF engine (its "Not in this repository" section places problem-specific evaluators outside the toolkit). Nearest integrity package `emitall/GUIDE.md` was read in full; it compares stored receipt claims but does not derive rooted agreement forests. A fresh one-shot X0 instrument is justified by the required zero code reuse and needed distinct exact partition/cut realizations. No existing problem evaluator is read or imported.

Skill ledger: prove-protocol, reading-contract, independence-bookkeeping, planted-truth, timing-discipline, tool-stewardship, and acceptance-gate read. This arm is X0 exact finite falsification only, not VERIFIED-CLOSED proof work.

## Pre-registered exact gate and lineage

Inputs: unmodified frozen-control file v1. All literal expected fields must match (partitions normalized only for unordered presentation). Exact integer/rational arithmetic; no tolerance. Negative controls must reject wrong topology, omitted optimum, omitted precut charge, failed tau halfbudget, false exponent; clean twin must pass. Comparator mutation: compare each expected value to one deliberately unequal value and demand failure. Source-edge enumeration does not call the partition evaluator; it removes literal edges, finds connected components, rejects label-empty components, and groups their labels. The two routes share only the specified labelled tree bytes and standard Python.

Oracle contact: frozen expected values were viewed before coding, as required. They may certify fixture reproduction, but may not be represented as held-out universal validation. Counterexample census instances will not be read from any production algorithm and the evaluator will not be embedded in a proposed safe-cover generator.

## Runtime plan (pre-launch)

First run only the frozen fixtures (at most four labels); measure fixture rows and exact cut/partition counts. Then pilot the counterexample census at increasing n starting n=1. Real progress is completed tree-pair/split rows written to receipts; retain per-pair timings. Stop on the first exact failure under a recorded balancing definition. Any change of n is remeasured; no unmeasured long census will launch.

Balancing search definition: one distinct source-edge cut with both label sides nonempty and maximum side size <= ceil(2n/3), the standard leaf-count centroid range. Search additionally records the stricter equal-halves subcase and whether max local d_D <= original b/2. Budget is original optimum b; require b>=1, cut count <=b, and seek zero surviving original optimum partitions. This is a precise finite hypothesis about arbitrary source splits, not the existential target.

## Frozen-control pilot executed

Script-of-record: `x0/exact_x0.py`, controls mode, through `./bootloops-python`. Receipt: `../../../results/algorithm-balanced-cover-x0-controls.json` (actual repository path `research/rmaf/results/algorithm-balanced-cover-x0-controls.json`). Exact executed summary:

```text
{"verdict": "REPRODUCES-ALL-FROZEN-CONTROLS", "fixtures": 9, "seconds": 0.004317165999964345}
```

Every literal expected value reproduced; no pin changed. The actual crossing has six original optima, two survivors, one additional cut, tau zero; the omitted optimum and successful clean twin are detected distinctly. The rational squared composed base is returned both as pinned raw 584775/160000 and exact reduced 23391/6400. Every literal comparator check rejected a deliberately unequal comparison value, and all six scientific negative control detectors fired as intended. Runtime is measured Python body wall time (launcher overhead not included; no complexity conclusion drawn).

Next pilot is complete n<=3 census; no unmeasured extension yet. Completed tree-pair rows and per-pair wall times are the progress units.

## n<=3 census pilot executed

Receipt `research/rmaf/results/algorithm-balanced-cover-x0-pilot-n3.json`. All 1+1+9 ordered tree pairs checked; 24 budget-admissible balanced splits at n=3, no failure. Measured n=3 body wall time 0.000474625 s for 9 pairs; small-input timing, not a claimed stable asymptotic rate. At n=4 the partition count rises from Bell(3)=5 to Bell(4)=15. Because this is a changed input regime, launch only a bounded 25-pair pilot, with early stop on an exact witness, instead of transferring n=3 speed as an ETA. No long calculation is planned.

## First n=4 candidate fire and stronger follow-up

Original centroid-ceiling census produced an exact n=4 failure in 0.00154525 s: source `(a,(b,(c,d)))`, target `(a,((b,c),d))`, original optimum b=1. Its first returned cut is 1:3 leaf-balanced under the pre-registered ceiling rule, tau=1, so it does not satisfy the local halfbudget condition. Receipt preserved as `algorithm-balanced-cover-x0-search-n4.json`. The n<=3 exhaustion establishes minimal n under this recorded one-cut search definition.

Additional hypothesis registered after that result: restrict the same census to equal leaf halves and require tau<=b/2; retain this as a stronger follow-up, not a revision of the first search. Both flags and original balancing definition will appear in its own receipt. At n=4 there are only 225 ordered pairs; the bounded same-regime first census already completed 14 n=4 pairs in submillisecond body time before its witness. Launch a bounded 25-pair stronger pilot with the existing early witness stop; no full long run.

Comparator hardening: added full expected-field corruption calls through `compare_fixture`. The first rerun stopped at the crossing because an older auxiliary corruption assertion assumed the uncorrupted expectation and also ran inside the deliberately corrupted fixture call. This is a test-harness implementation issue, not a frozen pin mismatch. The partial v2 receipt is retained; remove that auxiliary assertion and use the explicit full comparator mutation outcome. Fresh rerun will have a new receipt.

## Strong follow-up executed and replayed

Receipt `research/rmaf/results/algorithm-balanced-cover-x0-equal-halfbudget-n4.json`. Executed summary:

```text
{"verdict": "CERTIFIED-CANDIDATE-FAILURE", "n": 4, "source": ["a", ["b", ["c", "d"]]], "target": ["a", [["b", "c"], "d"]], "b": 1, "tau": 0, "local_halfbudget": true, "seconds": 0.0014554580000094575}
```

Cut edge source parent `R1` to child `R11`, descendant labels c,d, gives blocks {a,b}|{c,d}; one distinct nonredundant source-cut realization. Both local distances zero. Target overlap vertices `R1` and `R10` each have degree two in both block spans, so the source forest is an actual pure-bridge instance; it also belongs to the compatible/triple class. All three original optimum partitions are {a,b,c}|{d}, {a,b,d}|{c}, {a,c,d}|{b}. Zero refine the precut blocks. Exact completion adds one cut and total charge is two, versus original optimum one.

Separate `cut_graph_replay.py` contains no import/use of `exact_x0.py`. It independently enumerates source AND target literal cut sets at all q=0,...,n-1, matches labelled pruned rooted component graphs, and reproduces optimum cut1, the three optimum partitions, zero survivors, total charge2, and one source precut realization. Receipt `research/rmaf/results/algorithm-balanced-cover-x0-cut-graph-replay.json`. Executed summary:

```text
{"verdict": "REPRODUCES-WITNESS", "checks": {"original_optimum_cuts": true, "original_optimum_partitions": true, "surviving_count": true, "completion_total": true, "distinct_precut_realizations": true}, "seconds": 0.0009193329999561684}
```

Lineage limitation: cut-graph replay is a distinct algorithm authored in this same X0 context and first run on this witness. It supplies algorithm diversity, not fresh-nonauthor verification; no universal claim is certified by it. The primary evaluator's controls preceded every census. The replay's own frozen/corrupt fixture gate is retrospective and will be labelled as such if executed.

## Final frozen audit after comparator hardening

Original nine controls rerun unchanged in `algorithm-balanced-cover-x0-controls-v3.json`, with 41 literal comparisons, 41 full expected-field corruption calls caught, and six negative detector controls. Summary `REPRODUCES-ALL-FROZEN-CONTROLS`, nine fixtures, 0.005424458 s. Original v1 and partial v2 receipts retained; no pin mismatch and no fixture alteration.

## Verdict and open eligibility

Exact candidate failure: arbitrary globally leaf-balanced source splits need not preserve even one original optimum. The witness remains a failure even with equal halves, one admissible cut, tau zero, and both accepted completion-class memberships. Minimal label count n=4 in the executed one-edge balancing census; all n<=3 pairs exhausted.

This does not disprove existence of the target cover, does not prove any algorithm runtime, and does not certify reduction-history eligibility for the target's reduced-pair quantifier. Algorithm, Correctness, and Smaller base remain open outside this X0 finite result. No production generator was read, tuned, or constructed; no descendants spawned.

## Archive and handoff

`SCRIPT-HISTORY.json` records exact SHA256 agreement between preserved script snapshots (`exact_x0-v1.py`, failed `exact_x0-v2.py`, final `exact_x0.py`) and the corresponding receipts. Historical snapshots were reconstructed from the exact logged edit deltas and their hashes match; no historical receipt was overwritten. `VERDICT.json` is the machine-readable handoff with the full literal witness, all original optimum partitions, source cut, pure overlap geometry, acceptance counts, and limitations. Broad workspace toolkit validation was not run by X0; parent notified so any campaign-level suite receipt remains separate from this finite audit.
