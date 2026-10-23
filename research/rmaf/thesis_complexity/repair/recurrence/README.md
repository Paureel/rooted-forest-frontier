# Distinct recurrence/state-invariant route

Status: initialized. No universal runtime claim is accepted.

Owned scope: this directory; recurrence-specific result receipts/logs; recurrence-specific progress record.

Target: the literal Chapter 6 G4.1 P={a}, Q=empty, s=3 joint descendant bound, with reachable p=3 states, trivial merges/root removal, induction boundaries, and additive invocation offsets explicit.

Method: freeze hand controls, build an exact adversarial arithmetic/state check, then state the smallest falsifiable structural premise needed for a universally correct composition. Exact source cut patterns are required; arbitrary deletion closure is not an algorithm premise.

Isolation: no geometric-arm, adversary-proof/code, parent implementation, or correctness/transfer imports.

Planned artifacts:
- controls.md and frozen input ledger
- source-ledger.md
- state-invariant.md
- RepairArithmetic.lean
- check_recurrence.py
- result.json and report.md

## Toolkit decision (2026-10-14)

Consulted the full tools index and the nearest validation package, Gatekeeper's guide. Its integrity/CV tools handle numerical oracle dumps, not exact branching continuations or tree-cut legality. A one-shot exact rational continuation auditor and source-local tree control checker are justified; neither becomes a general toolkit package. Lean's kernel will check the generic composition theorem separately. Existing trace JSON is development/control input and cannot certify this route independently.

## Source reading checkpoint

Read the thesis text at printed pp104–109, 111, 117, 119–126. Missing PDF-extraction pages 110 and 118 will be recovered from the PDF before using their rules. Observed directly: invocation count includes the current call; trivial merges/root-removal happen within one invocation; P,Q are analysis sets distinct from protected edge sets; the source p≤2 assertion conflicts with the frozen p=3 control and is not imported. G4.1 A3BC resets P,Q in B, retains incoming sets in A, and adds the retained endpoint to P,Q in C (printed p123).

## Timing record

First exact-control pilot completed 26 named controls in 0.00294 seconds; the 37-row rational schema scan took 0.000188 seconds. The proposed multiplicative-measure scan used the same 37 schemas and took 0.000495 seconds including its hand checks. No large search is needed: the domain is ten credit states with explicit finite transition contracts. Lean pilot compiled the finite-state arithmetic; its first generic-composition compilation failed on unavailable List.Forall₂, retained in lean-v1.log. Replacing that unavailable library relation with an explicitly defined recursive PairBounds relation yielded the completed kernel check in 0.49 seconds. Negative-control compilation failed as required. No extrapolated multi-hour computation was launched.
