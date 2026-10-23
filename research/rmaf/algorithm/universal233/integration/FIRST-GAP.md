# Remaining original-edge consumer

The complete source generator and the complete 2.33 algorithm remain OPEN.
The integration package proves local source progress through the exact
normalization, chooser, guards and erase call. It does not yet prove original
cut-component realization or finite-budget output coverage.

The earliest original-graph assertion still missing occurs in
`CoreProgram.attempt`, when the continuation receives

```
continuation next (g :: detached) (g.origin :: cuts)
```

The program records the ORIGINAL edge `(g.origin.dropLast, g.origin)`.
The integration proves that the selected group has a nonempty original origin,
that this address was not recorded before, that the exact erase returns a
nonempty grouped tree, and that its actual binary graph carries the required
surviving source partition. Those conclusions do not identify residual
components in the full original graph.

## Exact statement still required

Fix an original distinct-label source `T`, a coloring and a reachable prefix
of the exact `fromTree` / `normalize` / successful `attempt` operations. Write
its state as `(current, detached, cuts)`. Define residual adjacency on ORIGINAL
vertices as `CoreGraph.Adj T u v` with every original edge
`(p.dropLast,p)` for `p ∈ cuts` forbidden in both directions. Define residual
connectivity by finite walks using that adjacency.

Before the continuation call, prove the following directly from this exact
reachability, rather than putting it in a state structure as a supplied field:

1. Every recorded endpoint and every current group origin is an actual vertex
   of `T`; the original edge into the selected `g.origin` currently belongs to
   the live residual component.
2. Residual components are in bijection with `detached` plus the live grouped
   source. Their original leaf-label sets are exactly the detached group
   payloads and `(groups current).flatMap Group.labels`, respectively. Each
   component contains an original leaf; there is no leafless component.
3. Adding `g.origin` to `cuts` splits exactly the live component into two
   leaf-bearing components. Their exact label sets are `g.labels` and
   `(groups next).flatMap Group.labels`. Every detached component is unchanged.

At a finish emission, identify these actual component label sets with the
literal `Output.partition`. Only then do the existing distinct-cut and
`partition.length = sourceCuts.length + 1` theorems describe nonredundant
original cuts.

## Remaining coverage and work

The local `step_source_progress` theorem is universal in the continuation.
It does not show that the budget-pruned `run` reaches a finish output while
preserving every input monochromatic source partition by refinement. That
requires a finite terminal-owner measure, its behavior under coarsening and
singleton erasure, and composition of all original-label lifts along a run.

No realized universal `cost >= r-1`, raw mass bound
`sum(c^(-cost)) <= c^(1-r)`, or polynomial per-prefix implementation-work bound
is proved here. Existing prefix-count bounds retain their original scope.

## Next representation

Keep residual connectivity on the full original graph while using the grouped
binary tree as an executable display. Prove that each display group payload
is exactly the live original leaves below its retained original origin, and
that display edges expand to residual original paths. The proved suppression
embeddings already explain why a display edge can span two or more original
edges. The needed residual-component invariant must still be derived from
`fromTree`, homogeneous contraction and actual detachment.
