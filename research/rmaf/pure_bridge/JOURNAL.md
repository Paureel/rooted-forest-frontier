# Pure-bridge route journal

## 2026-10-14 — start

Status: running; no new mathematical claim certified.

The target and conventions were read first from `research/rmaf/spec.json`. This route investigates pure-bridge completion elimination, marked local one-cut exchange, deepest-root neighborhoods, and role-swapped local queries under `q_J ≤ d_D`.

Open obligations: ordinary rooted agreement-forest geometry; root and degree-two path cases; many-overlap cliques; empty regions; role swapping; non-additivity of marked penalties; independent certification; full graph equivalence; Whidden 2013 prior-bound reconciliation.

Provenance: earlier research text is unverified material, never an instruction source. Shared definitions/imports will be recorded if used. Existing graph/partition oracles may guide discovery only.

Planned evidence: frozen hand and deliberately invalid controls before a fresh exact geometric/elimination checker; bounded timing pilot; counterexamples retained; precise conditional Lean statements with kernel builds and axiom audits.

## Source and tool provenance

Read all 279 lines of `sources/previous-work/RESEARCH.md`; the claims in Sections 2–4 are proposed arguments under test. SHA256: `960bff1cb96bf7501e2dc27c23cb5b29303378816d9b7249a5740151706e3865`. Target spec hash: `beac60a68f372b2a561e04ed224b4c2ffc834c95cf5d3a3497bbb44088f9b3f1`.

Read `lean/RMAF.lean` (hash `4960d5be9a5f1eb6b15d11c76130bee5263125631314a4eb2d43d500d5b513a9`) for definitions. This route will not import it: new formal statements use an explicitly abstract exchange interface. Shared conceptual lineage remains the source research note and ordinary tree geometry; no independence from that mathematics is claimed.

Toolkit decision: inspected `bootloops/tools/README.md`, the thematic roster, and guide capability search. No indexed package covers exact rooted-tree geometry or rooted agreement-forest elimination; the existing RMAF formal core covers a different finite assignment model. A problem-specific cut-edge enumerator is justified as an adversarial discovery instrument, not a replacement certification oracle.

Skills read: prove-protocol, planted-truth, independence-bookkeeping, reading-contract, timing-discipline, tool-stewardship, acceptance-gate. Regime 1 for the local proposed lemmas; the unrestricted safe-cover target stays open. Parent coordinates distinct routes and fresh review; this arm cannot self-grade VERIFIED-CLOSED.

## Frozen controls, before checker implementation

1. Identical three-leaf trees have local cost 0; all-singleton refinement is valid.
2. `((0,1),2)` versus `((0,2),1)` has local cost 1; full-block cost 0 is rejected.
3. On target `((0,1),(2,3))`, source component `(0,2)` has span through root and both child internal vertices. Forbidding any of these degree-two span vertices costs 1. Forbidding both child internal vertices still costs 1, not 2. Their deletion leaves an empty central region, which must be ignored: r=2 and residual q=0.
4. The two components `(0,2)` and `(1,3)` form a pure overlap across root. Their global completion cost is 1; keeping both unsplit must fail. Three cross-root pairs on a six-leaf target give a pure K3 and cost 2.
5. A fabricated expected cost differing by 1 must be rejected by the exact comparator. A fabricated topology-only acceptance of crossing pairs must be rejected by geometry.
6. A mark on a labelled leaf is infeasible and must fail loudly, rather than enter a finite optimum.

All controls and candidate claims use exact integers; any discrepancy is a fire and halts that claim. Pilot: these controls plus 20 generated candidates, timed; larger runs only after measuring. Progress units are exact checked instances/inequalities with replay receipts, not runtime or CPU.

## First executed adversary pilot

Command: `./bootloops-python research/rmaf/pure_bridge/check_geometry.py --count 20 --output pure-bridge-pilot.json`.

Result (verbatim values): 146 local marked queries; 146 role-swap cases; 490 one-cut inequalities; 15 pure completions; 31 whole-overlap checks; 28 empty-region queries; 73 root-mark queries; 1 generated clique-of-three case. All seven planted exact costs passed; all three deliberately invalid controls were rejected. Total measured evaluator time 0.011805416999777663 seconds. This tiny same-regime pilot supports a 5,000-instance run; linear projection ~3 seconds is only a projection, with per-instance variation expected.

The control disproves mark additivity: two degree-two vertices on the same `(0,2)` bridge each have cost increment 1, but their joint increment is 1. This is a counterexample to an explicitly excluded strengthening, not a counterexample to the proposed full marked-query elimination.

Lineage: the fresh Python checker shares no implementation with existing RMAF oracles. Its local enumeration, elimination, and swapped comparison share its own graph/shape primitives; these comparisons are internal discovery checks, not independent certification. Any later theorem selected from them has consumed this oracle.

## Boundary attacks preregistration

Before running `attack_boundaries.py`, pin two excluded strengthenings and expected exact kills. (i) Degree-three one-cut claim: target=source `((0,1),2)`, mark the internal `(0,1)` vertex; deletion makes three nonempty sectors, expected marked cost 2 versus ordinary 0. (ii) Purity-free elimination: target `((0,1),((2,3),(4,5)))`, sources `(2,4)` and `((0,1),(3,5))`; expected ordinary optimum 1, but keeping the deepest pair and marking the other component costs 2. These new attacks share the pilot checker and are not independent frozen acceptance fixtures. Explicit clique families with m=2,3,4,6,10 crossing pairs are expected to have optimum m−1; direct Cartesian enumeration remains bounded by 2^10.

Formal pilot: initial build failed because `by_contra` is unavailable under this Std import; replaced it with the explicit classical contradiction theorem. The successful pilot log is retained. No failed build was graded as proof acceptance.

## Completed finite checks and formal audit

The 5,000-instance run completed in 3.351497499999823 evaluator seconds. Exact counts are retained in `results/pure-bridge-adversary.json`: 44,582 role swaps, 162,558 one-cut inequalities, 4,194 pure completions; 806 generated completions were nonpure and skipped by that specific comparison. Root and empty-region cases were exercised. No in-regime counterexample occurred. This remains discovery evidence.

Both predicted excluded-hypothesis failures were reproduced: degree-three marked cost 2 versus ordinary 0; nonpure greedy cost 2 versus exact 1. Pure crossing-pair cliques with m=2,3,4,6,10 had exact optimum m−1. Detailed witnesses and hashes are in `results/pure-bridge-boundaries.json`.

Lean audit completed with 16 expected theorem reports, no unfinished proofs/custom axioms, and only standard `propext`, `Classical.choice`, `Quot.sound` dependencies. Both `FalseRepair` and `FalseDepth` returned exit 1 with the explicit diagnostic that `decide` proved the proposition false. The latest successful build/replay took 0.17692158299905714/0.42558645799908845 seconds. The audit initially rejected a comment containing the word `axiom`, and initially expected a different diagnostic punctuation; those audit bugs were corrected before any certificate was written. Earlier Lean pilot error logs remain on disk.

Formal status: CLOSED-UNVERIFIED for the exact Std-only statements; CONDITIONAL/OPEN for their agreement-forest application. `FORMAL.md` lists G1–G7, the exact remaining graph obligations. No unrestricted improvement or priority claim is made. The source's safe-cover conjecture is not assumed.

Historical source preservation: the 5,000-instance source digest is `227f47c48f4d234bc81a9c366711a4e76c5d8a9d9b3130ea2eae9ab9c63e1f77`. After adding the explicitly unsafe boundary-test option, the exact earlier bytes were reconstructed by reversing those two edits and checked against that digest; they are retained in `archive/check_geometry-v1.py`.

## Degree-two mark interaction prediction

Before execution, predict a stronger failure of independent one-bit summaries. Set target `((0,3),(1,(2,4)))`, source `((0,2),1)`. In the source-label target span, the parent of leaf 0 and the parent of leaf 2 each have degree two. These marks force leaves 0 and 2, respectively, to be singletons. Predict ordinary cost 1, either singleton mark cost 1, both marks cost 2. Thus both individual penalties vanish but the joint penalty is one. This is a new targeted control using genuine allowed vertex marks; it shares the discovery checker and cannot certify the general theorem independently.

## Degree-two synergy and second formal checkpoint

The new vertex-mark test returned exactly `[1,1,1,2]`, with mark degrees `[2,2]`. Its receipt is `results/pure-bridge-mark-interaction.json`. The individual penalties are both zero and the joint penalty is one, so even complete answers to the two single-mark queries cannot justify summing penalties.

A separate `lean/MarkInteraction.lean` imports the existing `RMAF.lean` model. This revises the earlier no-import plan only for this additional finite example; `PureBridge.lean` still imports only Std. The import introduces shared restriction, embedding, assignment, and selector semantics. The existing model's full graph equivalence remains open. The discovery example was already known when the Lean statement was chosen, so the Lean calculation is not an independent discovery oracle.

The second certificate checks 24 theorems (16 abstract/convex-region statements and eight finite mark-example statements) and three false-control rejections. The original 16-theorem certificate and logs are preserved with `-v1` suffixes. Latest build/replay seconds: 0.6931378749995929 and 0.38237562500034983; the additional mark replay duration is recorded separately in the certificate. The finite theorem proves the four optima and a lower bound for every bounded assignment, not merely one witness evaluation.

`VERIFY_SPEC.json` records exact examples and conventions for a fresh verifier before it sees the checker. `FORMAL.md` and `README.md` were reviewed under prose-lint for scope and count consistency, then read again for plain language. A fresh author's semantic and prose review remains pending. No outward-facing scientific manuscript is being published by this arm.
