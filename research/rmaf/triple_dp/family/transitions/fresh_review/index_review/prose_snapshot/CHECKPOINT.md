# Family merge result

For two actual indexed families with designated open boundaries, the Lean
constructor produces a merged family with exactly the original lifted
supports, except that the two boundary supports are joined through the
parent root. Every other index stays distinct. The output has
`L.blockCount + R.blockCount - 1` blocks and closed cost
`L.cost + R.cost`. Fresh nonauthor review confirms this exact interface,
including its existential support equations and all family fields.

The accepted main sources remain pinned in MAIN-MERGE-SHA256.json. The
earlier REPORT.md retains its historical pending-review status. The completed
review is `fresh_review/REPORT.md`, with machine receipt
`research/rmaf/results/triple-family-transitions-fresh-verdict.json`.
The reviewer rebuilt local dependencies from source in isolation, reproduced
the five positive fixtures and all malformed, wrong-number and support
controls with new graph code, and checked four exact false Lean claims
against separate correct twins. An import-error control was excluded from
mathematical rejection evidence. Only standard axioms appeared.

The main per-module query counts remain FiniteSelection 4, FamilyMerge 9,
MergeContract 7 and MergeControls 15. These are declaration queries, including
constructor definitions and finite control theorems; they are not a count
of new mathematical theorems. The reviewer added one consuming theorem that
uses only the exported universal interface. Its complete inventory and
dependency counts are recorded separately in the fresh review.

The independent geometry route also passed fresh review for its 17 support
statements. GEOMETRY-PREMISE-NOTE.md records the explicit left-root premise
of one root-path theorem. The independently authored index route constructs
a different enumeration and proves that only the two designated boundaries
are identified. It proves the merged count and an exact closed enumeration
of length `L.cost + R.cost`. Fresh review of that route is pending; no adapter
to the main index type is asserted. The main constructor was written without
reading either new supporting proof, and imports neither.

Live child restriction and the complete four-transition correspondence remain
open. Their next target and exact controls are pinned in
`restriction/TARGET.md` and `restriction/controls.json`; a separate adversary
is testing them before proof construction. The valid raw-family control with
a leafless open incursion is outside the required normal-form premise.
Normalization transport, color/mask legality, graph correspondence and
Python refinement still require their own universal results. No full G2,
safe cover, unrestricted algorithm or improved exponential bound is claimed.

The preservation check compared all 168 pinned files from the completed
family checkpoint and found no changes. The receipt is
`research/rmaf/results/triple-family-transitions-baseline-preservation-check-1.json`.
The scoped proof/control checks are recorded above; the general BootLoops
validation suite was not run for this increment.
