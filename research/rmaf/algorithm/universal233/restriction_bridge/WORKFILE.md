# Restriction/decomposition author workfile

Target: PUBLIC TARGET-v1.md, read 2026-10-15. Scoped proof status CLOSED-UNVERIFIED; author grade only. The public target pin is preserved.
All three main project milestones remain OPEN.

## Scope and dependencies
Only original `research/rmaf/lean/RMAF.lean` and the completed dependencies named in TARGET-v1 are admissible. No unfinished candidates are read. No child agents are spawned. No transport or cost conclusion may enter as a record field.

## Method and tool choice
BootLoops tools index and toolkit capability index consulted. Existing Lean wrappers and original RMAF definitions are the applicable instrument; the general integral/numerical packages do not implement literal rooted-tree restriction. New source in this directory is problem-specific proof and control code, not a toolkit engine.

## Fixed controls (before proof development)
Pinned in CONTROLS-v1.md and executed before developing universal proofs: nested restriction; selected-label LCA below root with unary suppression; disjoint local embeddings; false reverse for overlapping Q embeddings; wrong refinement direction; exact |F|-|Q| cost versus false |F|-1.

## X0 exact controls
Executed before universal proof development. `controls-positive.log` is empty with exit 0. `controls-false.log` retains all five `Tactic decide ... is false` rejections. All six fixed clauses passed (some grouped into conjunctions). Small fixtures are construction controls only. Pilot: original RMAF plus controls completed within the first short foreground job; no census or long job launched.

## Universal proof state
Restriction existence/labels: proved in Restriction.lean (`restrict_leaves`, `restrict_labels`, `restriction_exists`, `restricted_labels_exact`, `restricted_nodup`), compiled in restriction-dev03.log.
Nested restriction/idempotence: proved literally in `restrict_compose_mask`, `restrict_nested`, and `restrict_inside`; sameShape checker transfer follows in `sameShape_restrict_inside`.
Literal minimal-embedding transport: proved in Embedding.lean. The paired rooted-span/minimal and minimal/minimal disjointness equivalences survive unary suppression. The proof uses structural induction and the literal original address lists, including empty subtrees; it assumes only that B,C are contained in U.
Forward local agreement: proved in Forward.forward_local and assembled with component construction/labels in Forward.forward_decomposition. Q has no agreement or disjointness hypothesis.
Exact family cost: proved in Cost.exact_cost by unique original-label ownership, sum-of-filter-lengths exchange, and strict positivity of each local family.
Reverse reconstruction: proved in Reconstruction.reverse_reconstruction on literal Q.flatMap G. Actual Q partition/embedding checks, literal restrictions, and local agreement are input. Original agreement, exact cost, and global label permutations are conclusions. The frozen Composition.executable_span_monotone supplies only subblock span containment across distinct Q parents.

## First unfinished consumer
None within TARGET-v1: both requested directions are represented by unconditional theorems over their stated natural data. Fresh nonauthor proof/interface review remains unperformed by this author. The three global algorithm milestones remain OPEN.

## Replay and audit evidence
Replay-of-record: replay/20261015T090816Z/certificate.json. Source hashes match the frozen integration manifest for original RMAF and the three geometry modules. All 12 source modules rebuilt under an isolated LEAN_PATH and replay working directory. Complete origin audit covered 694 declarations including generated/private declarations; every imported module path resolved to the isolated directory or installed Lean runtime. Axiom union: Classical.choice, Quot.sound, propext.

Verbatim summary from replay-first.log:
```
"status": "PASS_AUTHOR_KERNEL_REPLAY",
"forward_decomposition": true,
"reverse_reconstruction": true,
"module_origin_total": 694,
"all_three_main_milestones": "OPEN"
```

The clean arithmetic plant passed; its false twin failed. Five pinned false claims failed. Missing axiom records, a wrong module path, a wrong module origin, a hidden custom axiom, and source-byte corruption were all caught. The hidden axiom lives only in PlantModel.lean in the hostile replay leg; production modules never import it. Development failures remain in *-dev*.log.

Scoped supplied toolkit check: `./bootloops-check emitall --par 1 --timeout 60` passed (bootloops-check-emitall.log). Other toolkit package batteries were not run because this change adds project-specific Lean proofs. No engine was unavailable. `bootloops-lean` and `bootloops-lake --version` receipts record Lean 4.35.0 and Lake 5.0.0-src+eb6cafb. No large census, raw standard-library declaration inventory, or long job was run.

## Independence and grade
The author creates the proof and controls and thus cannot supply independent certification. Any executable controls here share original RMAF semantics and are development evidence. Grade remains OPEN or CLOSED-UNVERIFIED until fresh nonauthor passes the pinned target and full interface trace.
