# Original-cut realization target pin (2026-10-15)

Grade at creation: OPEN; author development only. No children are authorized in this arm. Independent hostile/nonauthor review is arranged by the parent; this author cannot self-grade VERIFIED-CLOSED.

## Exact target

The frozen `integration/FIRST-GAP.md`, paragraphs “Exact statement still required” and “Next representation”, requires original residual components at `continuation next (g :: detached) (g.origin :: cuts)`. The edge is exactly `(g.origin.dropLast,g.origin)` on `CoreGraph.Adj T`, not a displayed edge.

Derive from exact `fromTree`, `normalize`, and successful selected leaf `erase` histories:
- recorded origins and current origins are original vertices;
- detached payloads and current payload are exactly leaf sets of all residual components;
- every component has an original leaf;
- the selected original edge splits only the live component, into `g.labels` and the next payload, preserving prior components;
- finish emissions identify those sets with literal `Output.partition` and hence give realized nonredundant cut charge.

Initial source is an ordinary rooted tree with distinct labels; no implicit rho. The complete algorithm, coverage, raw mass and polynomial work remain OPEN until separately proved.

## May assume

Frozen Lean proofs only with their printed hypotheses. In particular `GLeafErase` is constructed from exact erase on a unique-origin grouped leaf (`EraseLift.lean:erase_leaf_realization`); normalization is exact `CoreProgram.normalize`. Generic source leaf label uniqueness may be imported through the checked `leafAt_selected` and `singleton_selected_address_unique` bridge.

## Must not assume

Residual component correspondence, displayed-edge realization by one original edge, refinement/coverage, realized cost/mass/runtime, or nonemptiness of original residual components as an input structure field. Intermediate invariants may be used only after proving initialization and preservation from exact program operations.

## Representation route

Keep residual walks on all original vertices. Define a cut region by its highest vertex, excluding descendant cuts. Derive its connectivity and separation from literal parent/child edges. A recursively derived display invariant records exact original-live-leaf payloads both at a retained root and at its outer original ancestor, so root and internal suppression do not erase the original path.

## Controls frozen before implementation

Exact positive controls, using independently hand-specified tiny trees:
1. No cuts on a singleton: one leaf-bearing component.
2. Root suppression: cut one child of the original root and retain the whole original root path in the live component.
3. Nested prior cut: cut a descendant, then its ancestor, so the descendant component must remain unchanged.
4. Coarsened group with a prior detached descendant: the new group payload excludes the prior detached label.

Negative controls must be rejected:
1. Wrong-side cut claims labels of the opposite original root child.
2. Leafless residual component accepted after cutting both original child edges.
3. Nested ancestor cut reabsorbs the previously detached descendant.
4. A root-suppressed displayed edge is incorrectly treated as the literal recorded original edge.

Lean kernel compilation is the symbolic gate: all exact source dependencies replayed in isolation; no sorry/admit/custom axioms/native_decide; module-origin audit covers generated and private declarations; deliberately false statements rejected. Finite controls are development diagnostics, not universal proof and not independent author verification.

## Tool decision and timing

Toolkit capability index and emitall GUIDE were read. Emitall audits receipt claims but does not prove original-tree graph semantics or inspect Lean module-origin declarations. Extend the existing problem-specific Lean imports and reuse their replay pattern; new files are one-shot problem proof/evidence, intentionally not a new general toolkit package. All invocations use workspace wrappers. Runtime is unknown until the timed smoke pilot; no broad finite census is planned.
