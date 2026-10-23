# Algorithm X0 adversary workfile

Status: OPEN. Independent adversarial instrumentation only; no proof construction,
complete algorithm, improved exponent, or novelty claim.

## Frozen scope

Read TARGET.md and PIN.md before construction on 2026-10-14.
Own this directory and results/algorithm-x0-* only. Preserve all prior receipts.

## Required execution sequence

1. Consult toolkit and installed applicable skills.
2. Freeze literal n6, n7 and branching-recurrence controls before fresh execution.
3. Construct fresh rooted restriction, partition and vertex-span checks.
4. Run corruption/clean-twin, boundary, missed-cover and rational controls.
5. Measure bounded pilot; construct actual hard two-pendant-cut children.
6. Retain exact residual optima, partitions, spans, paid cuts and source applicability.

## Evidence

2026-10-14: toolkit index, local oracle and branching README documentation,
and seven named installed skills consulted. No existing oracle source code
read or imported. The toolkit's scientific evaluators do not supply this
object; existing project oracles cannot satisfy the zero-code-reuse X0
requirement. Therefore this is a deliberately separate, one-shot instrument.

`frozen-controls-v1.json` freezes the three literal receipt documents and
their SHA256 hashes; `control-spec-v1.json` freezes additional constructed
plants and the explicit nonempty missing cover before any oracle execution.

Fresh known-answer battery executed first:

```
PASS controls: 24 / 24; elapsed 0.0007464999999911015 seconds
```

Source read: split-or-decompose-v2.txt §2, PDF pages 3–4; §3.2, pages 6–7;
§6, pages 17–26 (including Figure16 and Lemma16). These definitions and
applicability tests are shared mathematical inputs, not independent theory.

Pilot executed after the 24 controls:

```
PASS pilot: 1 input state, 2 actual children; elapsed 0.006702792000055524 seconds
```

Bounded extension decision, recorded before execution: at most four receipt
states, same code/settings/machine, both orientations. Under equal per-state
cost the pilot gives 4 * 0.006702792000055524 = 0.026811168000222096 seconds;
the seven-label cases are a changed size, so this figure is only a nominal
floor and their own elapsed times will be retained. No large census launched.
The scientific progress unit is verified input states and actual cut children.

## Limitations

Finite checks cannot prove universal algorithm coverage or an exponent.

## Bounded outcome

Executed `run_x0.py --stage bounded`; retained log and full JSON receipt.

```
PASS bounded: 4 input states, 8 actual children; elapsed 0.0694664999999759 seconds
```

Measured kills: forced selected cherry increases optimum components 3 to 4
on both retained forced-baseline pairs; incomplete nonempty n6 cover requires
three initial cuts versus the original two; false bottleneck acceptance fails
the rational mass comparison. Endpoint lookahead fails on its retained n7
source-hard example: all cherry path parameters remain t=2 in both orientations.
No new macro candidate was supplied or tested, so no universal macro fire/no-fire
judgment can be inferred.

All eight actual two-pendant-cut children satisfy the published hard-call-site
exclusions, but singleton tidying leaves two forest components. They do not
represent the three-surviving-component bottleneck. Exact residual counts are
1,1,2,1 respectively across the four states, in both orientations.

Five source-predicate controls were separately frozen and executed after the
bounded run, explicitly as supplementary controls, and all passed. Full read
and inference provenance is in `source-ledger-v1.json`. Scientific prose and
number checks were applied to REPORT.md and README.md; no formal proof status
was promoted. This X0 owns no changes outside its directory and
results/algorithm-x0-*.
