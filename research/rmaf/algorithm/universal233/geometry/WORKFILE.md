# Vertex ownership geometry workfile

Status: OPEN. Owner: independent geometry agent. Scope is graph geometry and explicitly conditional composition only; source core and complete algorithm are not proved here.

## Consuming target
The first geometry consumer is the connected three-parent macro in `../../MULTICOLOR-INTEGRATION-v2.md`. It needs actual unsuppressed rooted minimal spans, nonempty leaf components after vertex removal, and original-label partition lifts.

## Planned claims
- Clique vertex Helly and polynomial selector.
- Region equivalence for avoiding subsets; nonterminal region bounds 2 or 3.
- Chain double-removal two-region coincidence; paid binary alternative.
- Conditional refinement/ownership cover with distinct-parent additive cuts only.

## Evidence ledger
- Read universal target and integration v2 in full before writing this skeleton.
- No sibling/core/safe-cover work read. No census repeated.

## Deliverables and gates
Retain exact hypotheses, Lean source and full axiom audit for accepted claims, rejected false control, and first remaining OPEN statement at its call. Do not count conditional core interfaces as proved.

## Incremental formal results
`Geometry.lean` compiled cleanly in `build-08.log` with wrapper `./bootloops-lean` (pilot 0.24 s, current compile 0.43 s). These are authored/development checks, not independent acceptance.

- `avoids_iff_monochromatic`: exact nonlabel avoiding equivalence for actual unsuppressed binary-address path hulls.
- `occupied_nonlabel_two_directions`: at least two realized deletion directions, each below three; no artificial rho needed.
- `two_region_coincident_occupancy`: two realized JOINT direction pairs plus occupancy of v,w in the whole parent implies occupancy equivalence for every subset piece. A leafless middle component contributes no joint leaf color.
- `median_on_three_paths`, `hull_convex`, `leaf_hull_helly_three`: explicit vertex selector and actual leaf-hull Helly, with no common-edge premise.
- `clique_three_survivor_cover`, `chain_four_ownership_cover`, `chain_two_paid_cover`: actual final-piece hull ownership covers. They have no recurrence/mass claim and assume only final disjointness, except the paid case also consumes coincidence.

## Leading representation debt (being worked)
At the integration consumer's first span call, need the theorem
`v ∈ RMAF.minimalVertices D t ↔ Hull (selectedLeafAddresses t D) v`.
The path-hull theorems above do not assume this seam and do not yet certify that executable list. Root suppression is forbidden in this seam: only `RMAF.restrict` suppresses unary vertices; the unsuppressed original address hull remains the collision object.

## Provenance / independence
No sibling work or core implementation read. `RMAF.lean` lines 109–133 read as development contact for the representation seam. All logs here are author-generated; no fresh nonauthor replay has occurred. X0 is parent-supplied complete and was not repeated. No numerical oracle/census was used in deriving graph theorems. BootLoops index has no rooted-MAF/Lean geometry package, so this one-shot theorem module is retained beside this campaign rather than registered as a numerical instrument.

## Superseding formal result
The earlier representation debt is now proved by `Bridge.minimalVertices_correct` (line 270). `RESULT.md` records the complete consumer trace. The final author audit has 129 theorem axiom reports and two rejected false propositions (`audit-run.log`, `axioms.log`, `certificate.json`). Original-label coloring, region counts, root convention, joint-region component equality, chain target distinction and concrete clique selection now have source-bound Lean proofs.

## Remaining obligations
- OPEN-STATE-ORIGINAL at macro entry: exact current-source-component original-label/history invariant, final-block ownership assignment and original source cut lifts.
- OPEN-CORE-REALIZATION at the core call: actual generator coverage/coarsening, nonredundant original-edge witnesses, mass and total work. `conditional_core_child_preserves_target` is explicitly conditional and does not prove these.
- Complete state machine, remaining source rules, recurrence, reconstruction and fresh nonauthor review remain outside this geometry arm.

## Prose review
Applied prose-lint meaning/honesty pass, then a separate wording pass to RESULT.md. No novelty or runtime acceptance claim is made. Referee-sim's fresh-context requirement remains pending for the parent's nonauthor reviewer; author notes do not fulfill it.

## Complete contact log
- Targets: `ALGORITHM-233-UNIVERSAL-TARGET.md` and `MULTICOLOR-INTEGRATION-v2.md`, full local source, read before skeleton.
- Existing executable semantics: `research/rmaf/lean/RMAF.lean`, read as development contact and rebuilt unchanged as an imported dependency; all its theorem axioms are included in the audit.
- Existing completed example: `research/rmaf/thesis_complexity/repair/geometry/Geometry.lean`, read during capability discovery. Its cut-flag model does not prove this target's leaf-hull geometry and was not imported.
- Tools index, project wrapper scripts, applicable local skills, and existing Lean file names were inspected. No current sibling/core/safe-cover contents or frozen census receipt was read.
- All finite controls and Lean elaboration logs here influenced development and cannot serve as independent verification. `audit.py` is an author source/axiom replay instrument; fresh nonauthor review remains pending.
