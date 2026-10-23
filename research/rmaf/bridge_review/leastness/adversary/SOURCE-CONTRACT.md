# Source contract and provenance (2026-10-14)

Read after controls/frozen.json and its SHA256 receipt were written:

* RMAF.lean:8–15 defines binary trees and the occurrence list of leaf labels.
* RMAF.lean:19–24 requires each Instance leaf list to permute List.range n.
  Therefore uniqueness of labels is an Instance property, not a Tree property.
* RMAF.lean:109–112 uses List Bool vertices and prefixes the side on descent.
* RMAF.lean:116–122 defines rootedSpan. Its node branch contains the exact
  expression `else [] :: (prependSide false ls ++ prependSide true rs)`.
* RMAF.lean:126–133 defines minimalVertices. The one-sided branches are
  `if ls.isEmpty then prependSide true (minimalVertices selected r)` and
  `else if rs.isEmpty then prependSide false (minimalVertices selected l)`.
* GraphRegion.lean:9–14 defines Adj by appending one Boolean and Walk by
  membership-preserving refl/step constructors. GraphRegion.lean:87–91 stores
  a nonempty connected support as first/rest. GraphRegion.lean:145–155 stores
  nonempty terminals, ambient inclusion, terminal inclusion and subset
  leastness against every connected ambient support containing the terminals.
* PureBridge.lean:10 declares `abbrev Address := List Bool`.

Source SHA256 values are retained in receipts/source.sha256. No new leastness
proof or previous Python geometry/oracle was read. The allowed whole RMAF file
was read. A 1–19 line GraphRegion extraction accidentally exposed the first
three proof lines of Walk.start; these are excluded from the independent
derivation and finite oracle. No other GraphRegion implementation proof body
was read. The MinimalEmbedding.region signature and defining expression were
also visible in the selected 145–161 range; no consumer proof was inspected.

The finite graph oracle is authored here. It constructs vertices and undirected
edges directly from the tree, enumerates every nonempty connected vertex subset,
and intersects those containing all selected occurrence vertices. It neither
calls nor translates minimalVertices/rootedSpan. The edge-deletion oracle
deletes each graph edge, computes its two components by graph traversal, and
keeps endpoints exactly when selected occurrences meet both components.
Selected occurrences themselves are always retained.

Shared layers: both independent finite routes share the tree incidence graph
and the exact frozen fixtures; this could hide a graph-construction bug. The
fixtures explicitly pin terminal/support addresses and Lean comparisons use
the unchanged source directly, so address-convention/source mismatch is tested.
Once the outputs are supplied to a prover, they are adversarial design feedback
and cannot count as fresh nonauthor certification of that prover's construction.

Runtime measures describe this audit only; no algorithmic complexity or faster
RMAF runtime conclusion is inferred.
