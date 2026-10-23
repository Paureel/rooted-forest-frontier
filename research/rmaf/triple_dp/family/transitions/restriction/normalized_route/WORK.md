# Concrete normalization premise transport

Status: CLOSED-UNVERIFIED for the supporting lemmas below; author check only, fresh review reserved by parent. Full restriction/recovery/G2 remain outside this arm.

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

Proof build 20261014T144627002683Z: all 16 build/control rows passed, including the concrete RawFamily and raw-versus-normalized premise checks. Actual axiom reports: normalized transports and exact support equalities use the three standard axioms propext, Classical.choice, Quot.sound; direct closed-region and nonboundary-index lemmas use propext only. No custom axiom or sorryAx in successful modules.

Final evidence amendment: make the raw false theorem attempt use the normalized theorem with a forged `rfl` equality to the untrimmed incursion, rather than feeding a negation proof to a positive goal. This is a stronger support-identity corruption detector; same preregistered false proposition. Add explicit conjunction showing convexity + root + a leaf alone do not suffice. Add target/X0 hashes and forbidden-declaration scan to receipt. These changes require one fresh rebuild.

Final build 20261014T144730845430Z: all 16 expected outcomes passed from a new empty olean directory, in 6.342154166 seconds summed compiler-call wall time. The forged equality was rejected specifically at `(normalize raw).openRegion = some incursion`. The current controls/target/X0 hashes and all dependency source hashes are in the receipt. No more source changes followed this build.

Protocol deviation: the workfile skeleton was written after the initial supporting-file reads, rather than immediately after the target-only read. The target was read first, controls executed before production construction, and forbidden new proof/checker bodies were never read. No independence claim beyond this recorded separation is made.

## Delivered interface

- `closed_support_exact`: normalized closed assembly index support is exactly the corresponding normalized closed support.
- `open_closed_support_exact` and `open_support_exact`: normalized open assembly preserves every closed support at `Sum.inl i` and the retained open support at `Sum.inr ()`.
- `normalized_closed_openBranchLive`: closed concrete assembly satisfies the premise because its boundary is none.
- `normalized_open_openBranchLive`: open concrete assembly satisfies the premise via `normalized_open_child_occupied` and `label_costRoute`, for the exact `R` and equality hypothesis passed to the constructor.
- `closed_region_child_live`: convexity, parent-root exclusion, and a leaf witness force every occupied child to contain a leaf. Proof uses the direct path through the parent root if the occupied vertex and leaf lie in different children.
- `nonboundary_child_live`: specializes that statement to any family index proved unequal to the boundary.

## Scope and independence

The raw fixture is a fully constructed `RawFamily`, not a collection of unchecked support claims. All three leaf values are 7. Closed indices remain separate; the root-containing support occupies the right child root without a right leaf. The compiled negation excludes raw branch-liveness; normalization retains its left leaf and deletes every right address.

The source lineage shares the old tree/address semantics, old normalization/path lemmas, concrete assembly definitions, and Lean kernel. RestrictionDefs is the sole new restriction module used. Its FiniteSelection dependency was copied, hashed, and compiled without reading its proof body; only its import line was read. No RestrictionGeometry, FamilyRestriction, new merge geometry, or another new checker body was read or imported by this route. This arm is a supporting premise transport, not an independently rederived normalization theorem.

Fresh verification and interface review remain reserved by the parent. This arm constructs no restricted child Family and proves no restriction count, transition cost/recovery, G2, or executable correspondence. The repository-wide `bootloops-check` suite was not run by this arm; the relevant isolated Lean build/control battery was executed and retained.
