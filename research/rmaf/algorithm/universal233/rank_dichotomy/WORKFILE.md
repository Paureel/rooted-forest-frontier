# Actual minimum-rank dichotomy — author workfile

Date: 2026-10-15. Target: `TARGET-v1.md`. Regime 1, adversary first.

## Scope and provenance

Own files: this directory and new `algorithm-universal233-rank-*` results.
Allowed dependencies are exactly the completed modules listed in the target.
No unfinished assembly completion, restriction bridge, pair proofs/reviews, or
other live candidates are read. No child agents. The completed all-colored X0
is declared development contact; its census and large raw receipt are not rerun
or read. All three full-algorithm milestones remain OPEN.

## Pre-registered controls

Executed before new proof construction by `run_controls.py`.
Receipt: `results/algorithm-universal233-rank-controls-20261015T091053Z/`.
All ten positive statements passed: contiguous one cost1 output; crossed
literal [2,2] with color-class embedding failure; all-distinct one cost3 output;
repeated-label refusal; q0 empty lists with pruned counts1/2; refinement
direction; exact crossed mass2/9 and factor2 identity. Three false propositions
were rejected. The first control banner mistakenly printed nine positive
statements; the executed source contains ten, and the final replay counts them
from the source. No expected value or test changed after proof construction.

## Source pin and import ledger

The source-bound replay rebuilds the exact completed45-module assembly-v1
dependency set, then six new modules. Original source pins, compiled copy pins,
and the source-coverage/cut/assembly immutable manifests are rechecked before
and after. `INTERFACE.md` identifies every conclusion and actual hypothesis.

A broad symbol search incidentally returned isolated line hits from forbidden
stack copies. Those files were not opened or imported; no proof uses them.
Every actual imported proof body is listed and hashed in the replay receipt.

## Proof state

1. Rank-r feasible implies unique literal output: AUTHOR_LEAN_PROVED in
   `MinimumUnique.feasible_unique`; exact original color-class memberships in
   `ColorClasses.feasible_unique_color_classes`; below-rank empty lists in
   `RankCost.below_rank_outputs_empty`.
2. Rank-r infeasible implies actual cost at least r: AUTHOR_LEAN_PROVED in
   `RankCost.infeasible_cost`, using original source-validity, monochromaticity,
   and the actual original cut/component count.
3. Actual raw-LIST mass sharpening: AUTHOR_LEAN_PROVED in
   `TailMass.generate_tail_mass` and `TailMass.infeasible_mass`. Its dyadic
   domain is discharged by the actual `generate_rawQ_mass` theorem.

The public target suggested proving forced operational steps. This arm instead
uses completed source coverage to obtain an actual cost-r-1 output, proves its
survival under budget enlargement, then applies actual dyadic mass saturation
and positivity of every literal list entry. The coordinator explicitly accepted
this as an equivalent proof route on2026-10-15 and requested that the original
target remain unchanged as history. No new operational trace theorem is claimed.

## Replay and failure controls

Executed `./bootloops-python .../rank_dichotomy/replay.py`.
Verbatim output:

    PASS author source-bound rank replay 51 modules 2194 declarations
    /Users/paurel/Documents/ChatGPT/bootscience/results/algorithm-universal233-rank-replay-20261015T091933Z

The inventory uses module origin for every declaration, including private and
generated declarations. Observed axiom union: `Classical.choice`, `Quot.sound`,
`propext`. Three false mathematical propositions rejected; missing-record,
foreign/private custom-axiom, and source-pin corruption plants caught.
`./bootloops-check emitall --par 1` passed its selftest. `./bootloops-lake --version`
reported Lake5.0.0-src+eb6cafb and Lean4.35.0. The full unrelated toolkit battery
was not run; no optional external mathematical engine is used by this proof.

## First unproved claim

Fresh nonauthor reconstruction and exact hypothesis/interface review of these
frozen statements. The canonical color-class feasibility test and its polynomial
tree/list work bound are explained in `RESULT.md`; this arm does not add a Lean
complexity model for that test. Neither claim is assumed by a proved theorem.

## Grade

AUTHOR_LEAN_PROVED / CLOSED-UNVERIFIED. Independent acceptance and the protocol's
fresh diversity/refutation passes remain pending. All three full-algorithm
milestones remain OPEN.
