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
