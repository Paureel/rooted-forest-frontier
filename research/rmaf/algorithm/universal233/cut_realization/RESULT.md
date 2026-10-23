# Original-cut realization and source-core coverage

Status: author kernel replay passed; independent hostile and nonauthor review are pending. The complete algorithm below 2.3391 remains OPEN. This package proves the source-core statements below and leaves raw mass and polynomial implementation work open.

## Source-core theorem

`ValidPartition.lean:52`, `checked_source_core`, starts with an ordinary distinct-label rooted tree `T`, a coloring, and an input block list `bs` satisfying the exact executable checks `RMAF.partitionCheck (leaves T) bs = true` and `RMAF.pairwiseEmbeddings T bs = true`. Every input block must be monochromatic. Its conclusion produces an actual output of the frozen `CoreProgram.generate T color (bs.length - 1)` with:

- the ordinary executable output partition check;
- `VertexGeometry.Refines bs o.partition`, meaning every input block lies wholly inside one output block;
- exact realization by the recorded original cuts, as defined below;
- monochromatic output blocks;
- `colorCount T color - 1 ≤ o.sourceCuts.length ≤ bs.length - 1`.

The budget convention is ordinary rooted `q = k - 1`; no root taxon is added. `InitialCoverage.lean:97`, `generate_refinement_coverage`, also permits any larger requested budget and handles the executable cap at `leaves.length - 1`.

## Original components

`OriginalGraph.lean:60` defines residual adjacency using `CoreGraph.Adj T` on all original vertices. It forbids both orientations of exactly `(p.dropLast,p)` for each recorded `p`. `ResidualWalk` is a finite walk in that adjacency. The proof retains original vertices omitted by displayed unary suppression.

`Realization.lean:109`, `generate_original_realization`, takes only membership in the actual generator's output list. It produces `RealizedOutput T o` (`Realization.lean:29`): an ordered list of full original components, rooted at `o.sourceCuts ++ [[]]`, whose leaf-label lists are the literal `o.partition`. The roots are distinct and pairwise disconnected, every original vertex belongs to one component, every component contains an original leaf, every recorded endpoint is an actual original vertex, and `partition.length = sourceCuts.length + 1`.

At a successful selected detachment, `History.lean:77`, `History.continuation_realizes`, derives the live literal incoming original edge, the exact selected payload and exact next live payload. `Realization.lean:116`, `History.continuation_components`, states the result with actual residual walks and proves that every prior detached component is unchanged.

The recursive `Models` invariant records exact live original payloads at both a retained origin and its outer original ancestor (`Display.lean:23`). The latter address represents paths omitted by suppression. `fromTree_models`, `normalize_models` and `gleaf_models` prove initialization and preservation. `History.invariant` derives the invariant from operation facts. Neither the final output theorem nor the external source-core theorem accepts a supplied residual correspondence.

## Finite coverage

`OwnerCover.lean:132`, `erase_owner_cover`, strictly shortens a finite list covering all current terminal owners after the selected singleton detachment. The surviving list still covers a nonempty grouped source. A strengthened normalization transport maps that list without changing its length and proves that every normalized terminal has a prior terminal preimage.

`Coverage.lean:92`, `run_refinement_coverage`, inducts on the executable budget. It transports each original input block through normalization and erasure and places that block in a final output component. `InitialCoverage.lean` constructs all representative and block-tracking hypotheses from the ordinary source checks; they are not external coverage assumptions.

## Executed evidence

The exact receipt is `replay/20261015T080042Z`; `Interfaces.log` prints the consuming theorem statements. `VERDICT.txt` reports:

> PASS: 28 isolated source builds; 1735 full module-origin declaration audits; 16 positive fixture theorems; 4 rejected false controls; 3 caught audit/pin plants

The inventory includes generated and compiler-private declarations. The observed axiom union is `Classical.choice`, `Quot.sound`, and `propext`. The audit rejected a custom axiom placed outside the proof namespace, caught a missing inventory record and a mismatched source pin, and rejected all four deliberately false cut propositions. The positive fixtures include original-root suppression and a cut below a later coarsened group; the latter group excludes the previously detached descendant.

The author replay uses copied exact source dependencies and only the workspace Lean wrapper. Its recorded build/audit invocations total about 30 seconds. No broad colored census was run. Failed elaboration logs remain in this directory. The general BootLoops package suite was not rerun because no toolkit package changed; the proof validation executed here is the isolated Lean replay. No unavailable numerical engine was substituted.

## Review boundary

The frozen core, geometry and integration sources are development imports. The receipt establishes kernel checking of the composed source-core proof, including all hypotheses printed in `Interfaces.log`. This author did not independently verify those imports, perform the required fresh-context hostile review, or run a novelty review. No novelty claim is made. `FIRST-GAP.md` states the next unproved consumers.
