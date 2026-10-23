# Independent charge route work plan

Read `../TARGET.md` first on 2026-10-14. Route: pointwise charges on an original finite parent enumeration, with two covering liveness predicates and overlap confined to one distinguished parent index. Derive closed costs from exact child-root indicators. This route is conditional finite combinatorics only: no restriction validity or geometric correspondence is assumed proved.

Owned sources: this directory and `research/rmaf/results/triple-family-transitions-restriction-charge-*`.

Must freeze exact positive and negative/twin numerical cases before proof code. Prohibited reads: new RestrictionGeometry, FamilyRestriction, RestrictionCounts, SupportRecovery, author/adversary checkers. Shared RestrictionDefs and old FamilyAssembly fields may be read. No children, custom axioms, sorry or native_decide.

Remaining stages:
1. Read applicable toolkit, proof/verification skills, prior finite enumeration and family-cost definitions, and frozen control specification/results.
2. Freeze independent numerical control data and independently check pointwise identities.
3. Implement generic list count/charge theorems and a conditional CostRoute Family consumer.
4. Execute isolated Lean builds, theorem queries, axiom checks, and proposition-level negatives; preserve attempts and pins.
5. Report theorem scope and remaining geometric/recovery obligations.

## Inputs and tool choice
Read old `cost_route/FamilyAssembly.lean`, its README, shared semantic
`RestrictionDefs.lean`, frozen `controls.json`, and X0 result receipt only.
X0 receipt reports NO-FIRE-BOUNDED, 3,530 candidates/257 in-regime cases,
all four transitions; no adversary implementation was read.
The general toolkit index has no finite Lean list charge instrument; use
Std Lean with isolated builds, extending the prior FamilyAssembly semantic
interface only. The new Python control/replay driver is problem-specific
and does not replace a general tool. No other new restriction source read.

## Gate and provenance
`CONTROL_SPEC.md` freezes exact positives/negative twins before proof code.
Expected data are pre-existing target fixtures, not regenerated output.
Own numerical controls and proof share this author's reasoning and fixture
spec; they are development evidence, not an independent certification.
Fresh nonauthor review is delegated by the parent outside this arm. Until
that review, at most CLOSED-UNVERIFIED for the conditional count/cost lemma.
Build runtime unknown initially: measure the first isolated dependency build;
no large search planned. Progress unit is checked named theorem/control,
not process liveness. Preserve source snapshots and every failed build log.

## Executed construction evidence
The initial numerical gate ran at 2026-10-14T14:51:13Z, before any Lean
proving run, with 8/8 exact positives, 8/8 wrong-output/clean twins caught,
4/4 malformed inputs rejected, raw nonlive-child-root incursion excluded,
and exact zero nulls. Receipt: `triple-family-transitions-restriction-charge-controls-v1.json`.
Measured dependency builds took 0.690 s (TripleDP), 0.318 s
(ConnectedRegions), and 0.530 s (FamilyAssembly). All subsequent theorem
builds took less than 0.5 s in the measured runs; no long compute requested.

`ChargeCore.lean` attempt 1 failed due to a membership rewrite, an incorrect
Std Boolean theorem name, and incomplete rewriting of option cases. The
source and diagnostic log remain in `attempts/ChargeCore-1/` and `logs/`.
Attempt 2 compiled. `ChargeConsumer.lean` compiled on attempt 1.
`ConsumerSentinel.lean` attempt 1 failed on reducibility of conjunctions;
attempt 2 compiled. The failed diagnostic's sorryAx arises from Lean's
failed theorem elaboration and is not accepted evidence; the completed
sentinel is separately queried in the final build.
The consumer sentinel constructs actual leaf/closeBoth families with two
identical leaf values (7 and 7), supplies all conditional premises, and
obtains parent cost 2 and child costs 0,0 from the conditional theorem.

Theorem scope: `count_balance`, `four_charges`, `conditional_family_count`,
`conditional_family_costs`; no actual restriction construction, support
bijection recovery, normalized premise transport, or full G2 claim.

## Final producer replay
`./bootloops-python .../charge_route/replay.py final-v1` completed with
`CLOSED-UNVERIFIED-CONDITIONAL-COUNT-COST` in the retained receipt.
Every allowed prior source and this arm's accepted theorem source was rebuilt
from copied source in `replays/final-v1/source/`, using Lean 4.35.0.
All 12 requested axiom queries report only propext/Classical.choice/Quot.sound.
The actual-family T1 sentinel has the same standard-only dependencies.
Four exact negative goals report `Tactic decide proved ... is false`;
`NoSuchChargeModule` is recorded separately as an infrastructure failure.

The initial numerical implementation used a truth-table comparator stub for
its mutant check. For the final replay this was strengthened to an actual
source-copy mutation of `equal_claim`, with all eight escaped wrong outputs
listed in the failing log. The initial implementation and receipt remain
unchanged in the attempts history/results; the stronger source and actual
mutant are retained in `replays/final-v1/source/`.

## Publication and review scope
README honesty pass: all count/cost statements carry conditional scope;
actual restriction construction and subtype identification remain explicit.
A second colleague-style pass removed completion language beyond the checked
statements. No novelty claim is made. This author cannot provide the required
fresh referee/semantic review; parent coordinator owns that subsequent review.
Broad toolkit suite was not run; no unavailable external engine was used.
