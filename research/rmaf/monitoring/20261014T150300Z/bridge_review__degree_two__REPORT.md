# Actual degree-two refinement

Status: the complete local and executable agreement-partition statements compile. Final source-bound replay and fresh nonauthor review are pending; this file makes no acceptance claim yet.

`lean/ActualRefinement.lean` composes the independent routes into three entry points. `actual_two_tree_split` takes the unchanged trees, selected block, actual finite degree, and restriction agreement. It produces two nonempty duplicate-free disjoint blocks partitioning the original block. Each block agrees between the trees; both pairs of exact supports are disjoint and nested in their old supports; both supports in the cut tree avoid the chosen vertex. The theorem needs unique labels only in the cut tree and does not require equal full label sets outside the block.

`actual_partition_split` replaces the block at an arbitrary position in the original agreement partition. It derives the block's nonemptiness, duplicate freedom, leaf containment and restriction agreement from the original Boolean predicate. It preserves that same predicate and arbitrary old marks in each tree's own coordinates, clears the vertex from the whole partition, and proves exactly one extra component and one extra tree-cut cost. `actual_component_partition_split` first derives degree two for an occupied nonterminal subpiece from degree two in a containing component.

The graph route derives support monotonicity from the completed exact leastness theorem. Removing a degree-zero or degree-one nonterminal would contradict minimality, so an occupied nonterminal has at least two neighbors. A nested support inside a degree-two support therefore has exactly two. The parent's one-tree construction chooses an actual child edge at the vertex, divides labels by leaf-address containment below it, and uses leastness to prove the two exact supports are disjoint and avoid the vertex. `actualDegree_two_iff` equates the executable distinct-neighbor count with this graph predicate. Unsuppressed path vertices are retained throughout.

The restriction route independently derives restriction associativity and preservation of rooted isomorphism under restriction. It then proves a five-Boolean summary of span emptiness and span/minimal-support intersections composes exactly at a tree node. The summary is invariant under pruning, unary suppression and child swaps. Consequently agreement on B preserves the exact support-disjointness Boolean for every A,C contained in B. This transports disjointness, without equating addresses across trees. The route's pinned clade plan was amended explicitly to this direct recursion; no graph-route implementation was read.

## Consumer trace

| Original use | Proven supply | Scope |
|---|---|---|
| Both `partitionCheck` conjuncts | Nonempty replacement blocks and `(b0 ++ b1).Perm B` preserve flattened label counts and leaf membership. | Same original label lists. |
| `all (restrictionAgrees t u)` | Hereditary agreement from proved restriction composition and RootedIso restriction. | Actual original restriction function. |
| `pairwiseEmbeddings t` | Exact one-tree split, support nesting, and list replacement. | All old pieces are retained. |
| `pairwiseEmbeddings u` | Exact support-disjointness transport and support nesting in u. | Addresses remain tree-specific. |
| G3 component-to-piece degree | `actualDegree_propagation` plus occupied and nonterminal premises. | Nonterminal is explicit; degree-three extension is excluded. |
| G4 unique occupied piece/global clearing | `pairwise_other_avoids` and `replacement_clears_vertex`. | List position is arbitrary; no implicit uniqueness of a chosen index. |
| Every old mark | Exact support containment in its own tree. | Arbitrary predicates, with no additive-penalty assertion. |
| One-cut cost | Exact `pieces−1` increment, and `replacement_forest_cost_bound` for fixed component count. | Ordinary partition count arithmetic. |
| `ExchangeSystem.clearRest` | The concrete agreement-partition repair supplies its one-piece geometric operation. | A full remainder-state realization, all rest-valid invariants and the other exchange fields are not constructed here. |

This increment supports G3/G4 in the exact executable model specified by the target. It does not instantiate the full `ExchangeSystem`; G2, G5–G7, fixed-witness compatibility, safe cover, runtime improvements and novelty remain outside the claim. Previously completed source files are unchanged. The earlier graph-route `TRANSPORT-OPEN.md` records that route's historical boundary; the new composed theorem discharges the missing transport using the separately completed restriction route.

## Evidence and independence

The target and parent controls were frozen before general construction. A fresh graph-deletion adversary ran first: 40 controls, 2,488 in-regime local witnesses, 2,632 partition refinements, and 3,464 degree-propagation checks, with no fire. Its 0.09345-second pilot is bounded evidence, not a proof. Both routes retain all failed elaboration attempts and separate malformed diagnostics from deliberately false propositions.

The parent authored the earlier leastness proof and shares its source lineage with the graph proof and one-tree construction. The restriction route used only the target and unchanged RMAF definitions, with no graph, leastness or parent splitter implementation read. Lean's kernel and actual source definitions are shared. Author compilation and source audits are not independent semantic verification. The fresh reviewer first froze literal controls and wrote new graph/partition code without importing either route or earlier checkers; its initial 42 exact checks, six required mutation catches, and joint-mark optima 1,1,1,2 passed. Its final report and source-bound verdict will determine acceptance.

The parent replay driver initially failed closed on a mislocated completed source, then on an over-specific false-diagnostic parser. Both scripts and diagnostic logs are retained. The corrected parser requires Lean's explicit `Tactic decide ... is false` message and excludes missing imports, unknown identifiers, and type mismatches. Neither diagnostic failure was counted as a semantic negative control.
