# Independent graph-deletion route

Status: finite adversary-first checks passed; ordinary route pinned; universal
actual degree propagation compiles; full formal refinement remains open.

The target was read before this skeleton's initial creation. Only graph_route/
was edited. No previous checker or sibling restriction-route derivation was read.
The initial control and pilot freezes remain unchanged.

## Executed evidence

Verbatim summaries from pilot.log and lean-controls.log:

```
controls: 40
in_regime: 2488; consumer_refinements: 2632; degree_propagation: 3464
verdict: NO_FIRE_WITHIN_BOUNDED_PILOT
positive_modules: 8; explicit_false_controls: 6
```

The pilot completed in 0.09344633299951965 seconds. No larger census was launched.
The six mutations were wrong degree, missing path, wrong root, cross-tree address
identity, overlapping label blocks, and wrong component cost. Their Lean twins
failed with an explicit false-proposition diagnostic. Failed development builds
are retained separately and do not supply proof evidence.

## Ordinary mathematics

ROUTE.md and route-freeze.sha256 contain the independently derived graph route.
The source deletion produces two terminal-containing components. The separate
G-prop argument transfers degree two from a component support to a selected
piece. The G-transport paragraphs explain the additional contraction/restriction
bridge needed in another tree. The unchanged agreement-partition consumer is
conditional on the full local refinement.

## Universal Lean intermediate

DegreePropagation.lean proves graph leaf removal, at least two neighbors at a
nonterminal of a least connected support, actual support monotonicity, and actual
degree propagation. Its `ExactTwo` predicate names exactly two distinct neighbors
under GraphRegion.Adj, retaining all actual address vertices. It is a semantic
statement of undirected degree two; no separate theorem equating a numerical
filter length to ExactTwo is claimed.

All final axiom reports are restricted to propext, Classical.choice, Quot.sound.
DegreePropagationControls.lean applies the theorem to a strict selected sublist
and proves the executable edge Boolean equivalent to GraphRegion.Adj.

## Remaining obligations

TRANSPORT-OPEN.md states the remaining source-cut existence, cross-tree
restriction/disjointness transport, and general agreement-partition replacement.
G3/G4 and the full clearRest instance remain open in this arm. Independent
nonauthor proof and fixture review is pending. No aggregate theorem count,
novelty claim, or project-wide validation result is registered here.
