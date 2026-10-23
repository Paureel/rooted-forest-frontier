# Depth-zero/one pretest author workfile

Status: OPEN. All three main milestones remain OPEN. This arm owns only `depth_one/` and new `algorithm-universal233-depth-one-*` receipts. No fresh nonauthor reconstruction has yet occurred.

## Target and restrictions
Read `TARGET-v1.md` on 2026-10-15. Implement actual original-edge enumeration, literal source component leaf sets, and actual `RMAF.agreement`; prove exact 0/1 minimum and an actual nonredundant original witness. Unfinished state cherry completion, kept parent, scheduler, review, and liveproof artifacts are barred.

## Preregistered controls, before proof
Identical original trees -> 0; `RMAF.Controls.leftTree/rightTree` -> 1; crossed balanced quartet -> rejection and minimum 2; singleton -> 0; absent/repeated labels -> refusal. Reject false whole-B two-color cut on crossed quartet. Include actual suppressed original edges.

## Tool selection and gate
The toolkit index was read. Existing completed RMAF and universal233 Lean proof modules and source-bound replay harnesses cover the formal task; this arm will extend/wrap that stack rather than introduce a general mathematical engine. Exact kernel proof plus executed positive/false and corruption/source-pin controls is author evidence only. No VERIFIED-CLOSED claim without fresh nonauthor reconstruction/interface review.

## Evidence
Pre-proof controls and the completed source-bound replay are recorded below.

## Proof chain
`Lemmas` -> `Reconstruction01.source_two_split` -> `two_block_complete` ->
`Optimality01.candidate_complete` -> global minimum / rejection lower bound ->
`Witness01.found_original_minimum`. `Runtime01` proves structural work bounds;
`RUNTIME.md` contains the source-level operation count.

## First open consumer
Fresh nonauthor reconstruction and interface review. See `FIRST-GAP.md` for the
optional stronger formal machine-cost consumer and the excluded main algorithm.

## Audit and limitations
Full module-origin/axiom and corruption controls passed in the author replay.
Independent certification is reserved for a nonauthor. Frozen upstream sources
and receipts are preserved. No novelty claim is made.

### 2026-10-15 controls and basic checker transport
Executed `dev.py RMAF CoreGraph Pretest Controls` before universal proof; all four modules accepted. `dev.py FalseControls` rejected all four pinned false claims with `is false`. Author development contacts only. The 30 completed dependency modules then rebuilt in isolation. `Lemmas.lean` now kernel checks: original vertex/edge completeness, subtree membership by original leaf addresses and prefixes, subtree label uniqueness, checked partition counts, selection-list transport, and two-block agreement invariance under within-block permutation and block swap. These are author builds, not fresh certification.

### Source-bound author replay and retention
The initial source-bound replay `replay/20261015T101012Z` passed 38 positive
source builds and audited 2,038 declarations; its positive/false, missing-record,
module-path/origin, foreign-private-axiom, byte-corruption, and source-pin
controls all fired as specified. `bootloops-check emitall` passed. The final
replay corrects a harmless name-list typo in the hostile custom-axiom audit;
the production inventory already covered every positive module. Both receipts
are preserved.

The first development helper overwrote its convenient latest log on each run.
All 47 early development Lean runs, including 9 nonzero runs (one is the
deliberate false-control run), have been recovered without modification from
the launch wrapper's retained manifests and append-only events into
`development-history/`. Later development invocations also retain source
snapshots directly. No failed run was dropped from the recovered index.

### Document checks
Applied `prose-lint` twice to README/RESULT/RUNTIME/FIRST-GAP: checked claim
scope and number provenance first, then plain-language wording and repeated
claims. The runtime theorem boundary is stated in the result and beside the
operation count. A fresh-context referee simulation remains for the parent
review; an author-context pass cannot satisfy that skill.

### Direct source-color supplement
The original registered `whole_B_false_one_cut` test checked actual source-edge
target agreements. Added `SourceColorControls` to exercise the completed source
generator directly: crossed two-color quartet has zero outputs at budget one,
two outputs at budget two, and the two whole color blocks fail the source
embedding check. These additional author contacts were pinned after the
universal proof and before execution in `CONTROL-SUPPLEMENT-v2.json`.
The first supplemental false-control source failed name resolution because
two opened namespaces both defined `Controls.crossed`; that is an elaboration
failure, not a rejected proposition. Version 3 preserves that draft and pins
a fully qualified false-control file, which Lean then rejected with `is false`.
The failed supplemental replay and all earlier replay receipts are retained.
The final replay is `replay/20261015T101515Z`; it audits all 39 positive source
modules and runs both the four original false claims and the repaired direct
source-color false claim.
