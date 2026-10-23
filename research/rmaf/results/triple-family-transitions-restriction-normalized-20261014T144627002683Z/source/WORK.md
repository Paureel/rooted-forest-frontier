# Concrete normalization premise transport

Status: IN PROGRESS; author check only, fresh review reserved by parent.

1. Target: transport `OpenBranchLive` through the concrete closed/open assembly constructors applied to `normalize F`, with exact support equations; no use of `normalized_assembly_exists` as support transport.
2. Allowed lineage: old FamilyModel, FamilyTrim, FamilyGeometry, FamilyTransport, PathStem, FamilyAssembly, core tree/address semantics; shared new RestrictionDefs only. No other new restriction proof/checker bodies read.
3. Organizing route: expose constructor supports definitionally, apply `normalized_open_child_occupied`, transport the leaf label to `CostRoute.LeafAt`.
4. Separate supporting geometry: a convex region excluding the parent root and containing a leaf cannot occupy a different child from that leaf, by a direct root-path witness argument.
5. Frozen controls: to be pinned before proof construction; positives and matching malformed/false controls must execute before main proof.
6. X0: parent reports finite-only PASS in `triple-family-transitions-restriction-adversary-hunt-v1.json`; receipt must be read and pinned before execution.
7. Build: isolated fresh source/olean tree, Lean 4.35.0 through workspace runtime, retain all failed attempts, print actual axioms.
8. Outcome: OPEN until kernel checks and controls execute; no full restriction constructor, transition recovery, or G2 claim from this arm.

Toolkit consultation: tools/README reviewed by capability; no general numerical tool implements these project-specific Lean declarations. This arm adds one-shot theorem modules and a local build receipt driver, not a reusable toolkit instrument.

Control attempt 20261014T144235500577Z: clean label rejected because `LeafAt` lacks an automatically synthesized Decidable instance; no production proof constructed and no negative counted. Control source v1.1 unfolds the same exact proposition with `change` before `decide`; statement and expected verdict unchanged. Snapshot of failed attempt retained.

Controls 20261014T144300253064Z: clean source compiled, false side flip rejected by `decide`, malformed identifier rejected distinctly. Production construction began only after these controls passed. X0 receipt read: 3530 candidates, 257 in regime, NO-FIRE-BOUNDED (finite only).

Proof attempt 20261014T144508379188Z: normalization premise transport and support equations compiled; separate closed-region proof hit unavailable Std tactic `by_contra`. Replaced with `by_cases` and explicit `False.elim`; retained failure. No theorem with `sorryAx` is accepted.

Proof attempt 20261014T144541141436Z: entire production module passed. Raw fixture helper hit nonexistent `List.IsPrefix.antisymm`; corrected to the standard `eq_of_length_le` with the reverse prefix's `length_le`. All statements unchanged and failure retained.
