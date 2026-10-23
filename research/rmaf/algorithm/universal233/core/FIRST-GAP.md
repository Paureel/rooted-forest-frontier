# Exact first unresolved source-core statements

The complete colored-source core remains OPEN. The local graph lemmas do not
justify the recursive production call yet.

## External source interface

At the ordinary solver's call `generate T color q`, an input agreement partition
is represented by a block list `bs`. The existing executable model checks
`RMAF.partitionCheck (RMAF.leaves T) bs = true` and
`RMAF.pairwiseEmbeddings T bs = true`. This arm has not proved the following
bridge from those exact Boolean conditions to its actual graph-support model:

For every `T` with distinct leaf labels and every such `bs`, construct
`P : CoreGraph.SourcePartition T` such that, for all actual leaf occurrences
`LeafAt T u x` and `LeafAt T v y`,

```
P.owner u = P.owner v ↔ ∃ b ∈ bs, x ∈ b ∧ y ∈ b.
```

Each `P.support i` must consist of actual source vertices, be connected by the
proved one-edge `Walk`, and be disjoint from all other supports. This assertion
has not been supplied as a structure field or imported from a pending theorem.
The module defines ordinary connected-support source semantics directly. The
conversion from the existing minimal-embedding checker remains a consumer
obligation. No claim about target restrictions follows from this source-only
model.

## First internal call

Even if the caller supplies a source partition in the connected-support
semantics, the first internal unresolved statement occurs at
`CoreProgram.lean:110`:

```
let t := normalize current
```

The exact needed assertion is a graph simulation of this particular operation:
for every reachable current grouped tree, every valid monochromatic source
partition on its expanded original labels admits a valid monochromatic
coarsening whose blocks are unions of the normalized groups; contracting each
normalized group gives a valid partition on the actual binary graph underlying
`t`, and expanding those grouped leaves recovers that coarsening with the
original-label refinement relation preserved.

`CherryCoarsening.homogeneous_cherry_coarsening` proves the local coarsening on
one actual graph. It does not prove the grouped-tree quotient map in the
previous paragraph. In particular, after unary suppression, an edge of the
current skeleton can represent an original path rather than one original edge.
The current program retains original addresses, but that retention alone is no
graph simulation proof.

At `CoreProgram.lean:113` and `:114`, the proved unique-color and mixed-cherry
singleton statements need a second simulation: deleting that singleton group
and suppressing unary vertices must transport the surviving source partition
and its refinement lift to `erase g.origin t`. The local singleton theorem does
not prove that simulation.

## Original cuts

At `CoreProgram.lean:105`, the program records `g.origin` as the original edge
`(g.origin.dropLast, g.origin)`. The proved record invariants exclude the empty
root address and repeated addresses. The missing graph assertion is:

For every reachable prefix, deleting exactly its recorded original edges from
`T` yields exactly one component for each detached original-label group and
one component for the live original-label set, with no leafless component.
Every recorded endpoint must be an actual source vertex. Suppressed paths and
root suppression must preserve this invariant. At an emission this assertion
must identify the original connected-component label partition with
`o.partition`.

Without this assertion, `pieces = recorded cuts + 1` proves a syntactic count,
not nonredundant original cuts. The universal bound `cost >= r-1` and raw mass
bound have not been proved for realized core outputs.

## Different organizing route

Keep the complete original graph throughout the proof. Define residual
connectivity by finite walks that avoid the recorded original edges. Maintain
one leafbearing residual component for every detached group and one leafbearing
live component. Prove partition coarsening and singleton detachment on those
components before defining any suppressed representation. Treat suppression as
an executable display of the live component, with a separately proved map from
each skeleton edge to an original path. The local walk-pruning and homogeneous
coarsening theorems already operate on unsuppressed graphs and can be reused.

This route separates the component invariant from contraction code. It still
requires a proof; it is a proposed next representation, not an assumed rescue.
