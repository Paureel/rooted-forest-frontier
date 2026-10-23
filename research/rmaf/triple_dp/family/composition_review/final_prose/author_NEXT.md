# Remaining family correspondence target

This file records the next universal obligations after normalization and the
forward representation map. It is a target, not a proved result. Preserve the
current Lean sources and receipts when implementing a later increment.

## Merge the two distinguished open indices

Let `L : CostRoute.Family l I` and `R : CostRoute.Family r J`, with
`L.boundary = some i` and `R.boundary = some j`. Construct a family on
`BTree.node l r` by retaining every nonboundary child index separately and
replacing those two distinguished indices with one root-containing index.
Its support is the left lifted support of i, the right lifted support of j,
and the parent root. Prove every output family field from the input fields.

The merged block's leaf-label membership is the union of the two input open
blocks. All other blocks preserve their respective membership. The required
count is `L.blockCount + R.blockCount - 1`, and required cost is
`L.cost + R.cost`. The output is geometrically a family regardless of colors;
whether a DP rule permits the merged label block is a separate admissibility
obligation. Do not identify any other indices, even when colors agree.

## Restrict a normalized parent family

Construct actual child families, selecting and reindexing only live support
restrictions. The normal form is essential: an arbitrary raw open support
can enter a child without a leaf, as the frozen incursion fixture shows.
The proved normalized occupancy theorem excludes that case geometrically;
the child family and charge equations still have to be constructed.

A closed parent region avoids the parent root. Its convexity should force it
to lie in one child, where it is leaf-bearing. A normalized open parent region
restricts to a retained child-open region exactly in the children containing
its leaves. A child root may instead belong to one of the parent's closed
regions. Selecting that region as the child boundary changes its child cost,
so the parent cost equation must account for closing it at the transition.
These are proof obligations, not assumptions supplied by `RawFamily`.

Classify the result by the parent open region's occupancy: absent, left only,
right only, or both children. Prove correspondence to close-both, extend-left,
extend-right, and merge, respectively, including all four exact tolls.
Unused internal vertices remain allowed. No discarded leafless fragment may
receive an index, leaf block, boundary state, or charge.

## Acceptance boundary

Use the pinned existing positive, malformed, wrong-result and clean-twin
controls before proof construction. Freeze any new merge/reindexing controls
before examining their computed outputs. Obtain fresh semantic, axiom and
control review of each universal increment. Exact finite fixtures support
the harness but do not establish these statements.

Closed-hull/executable span correspondence, good-color/bad-mask legality,
automaton instantiation and Python table/backpointer refinement remain
separate interfaces. The forward representation functions preserve supports
definitionally; `normalized_assembly_exists` itself exports only existence,
cost and block-count equalities. Consumers needing exact supports should use
the concrete functions or a strengthened theorem proved from them.
