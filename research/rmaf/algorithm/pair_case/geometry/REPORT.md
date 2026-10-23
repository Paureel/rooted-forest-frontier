# Actual pair-geometry selector

G is author-checked in Lean for the exact original-tree hypotheses of TARGET-v1. The executable selector returns either a shared three-region vertex or an oriented original target edge with four nonempty original-label sectors and both full mutual-clear predicates. Fresh nonauthor source replay and consumer review remain required before scoped acceptance. The complete algorithm, correctness and smaller exponent remain OPEN.

## The proved selector

`lean/Selector.lean:actual_selector_exists` starts with an original `RMAF.Tree`, distinct original leaf labels, disjoint selections A,B, and an actual nonempty `RMAF.minimalVertices` intersection. It returns a shared vertex where executable `regions` has length three for A or B, or a pair `(p,p++[s])` belonging to the executable original `edges t` list. Both endpoints lie in both actual parent embeddings. For the child v, executable `descendants t v` locates each original label at its unique full-tree leaf address and tests the original prefix v. The four `sideLabels` lists are nonempty and satisfy full mutual clearance against the other unsuppressed parent embedding.

`choose` scans the original vertices and then original edges. It first rejects repeated original labels, repeated selection labels, empty selections, absent labels and non-disjoint parent labels. `choose_sound` proves every returned choice has its exact original-graph meaning. `choose_complete` proves it returns a valid choice on every proper input with nonempty overlap. `choose_binary_when_two` supplies the narrower target: when both executable region counts are two at every shared vertex, the returned choice is an actual oriented edge. `choose_none_without_overlap` covers the disjoint and singleton-overlap exclusions.

The proofs import only frozen `RMAF`, `Geometry` and `Bridge`. No source-core, exchange, cut realization, state history, asymptotic solver or selector/mutual-clear premise is imported. `ClearEdge` and `ActualClear` are conclusion predicates, and neither appears among the selector's input hypotheses.

## Original-address argument

`region_child_iff` and `region_up_iff` identify the actual child and parent directions. `realized_neighbor` proves that an occupied direction at an occupied nonlabel hull vertex is equivalent to an adjacent hull vertex in that direction. Two pairs of occupied directions in the three-direction address tree have a common direction, yielding an original shared edge. `minimal_vertices` and `child_actual_edge` connect its endpoints to the finite original executable tree and edge list.

If a sector of that edge intersects the other parent hull, choose two sector labels a,b whose path witnesses the collision, and an opposite-sector label c. The other parent hull intersects each of the three paths a–b, a–c and b–c: one intersection is the collision, and the other two use the shared edge endpoint. The three paths intersect pairwise at a,b,c. `helly_four`, proved from the frozen address-path convexity and three-set Helly theorem, supplies a point common to all four sets. At that point the three selected labels occupy pairwise different regions. The actual disjoint-leaf overlap theorem excludes a selected label at the common point, so this is a shared three-region vertex. Excluding that alternative proves both full mutual-clear statements for the edge.

The proof uses original addresses throughout. It does not replace an original path by one displayed restriction edge. At the original root the upward direction is absent; the same construction can choose either actual child edge.

## Actual hull degree

`hullNeighbors` filters the original parent/child neighbor list by the actual executable parent embedding. `neighbors_nodup` and `hullNeighbors_nodup` prove the list counts distinct vertices. `hullNeighbors_actual` proves membership is exactly actual original-edge adjacency to a vertex in the parent embedding. `region_count_actual_hull_degree` proves that its length equals the executable occupied-region count at every occupied nonlabel parent vertex. This supplies the requested actual degree bridge without assuming it as a record field.

## Scoped work

The source defines `findCalls` and `chooseCalls` for the actual finite scans. `vertices_length`, `edges_length` and `chooseCalls_linear` prove at most 4n−3 candidate-predicate evaluations for a tree with n leaves. The proper-input check, construction of original addresses, and each predicate also perform work and are excluded from that predicate counter.

All operations in a predicate are fixed-depth compositions of structural tree traversals and finite list scans. Each traversed list has polynomial size in the original input; an original address has length at most the number of vertices. The deliberately simple code recomputes embeddings and descendant lists, so the overhead is polynomial without a tight implementation claim. No optimum oracle, partition enumeration or parameter-dependent exponential search occurs in `choose`. The full solver's work and original-state history are outside this scoped result.

## Executed controls and replay

`results/algorithm-pair-case-geometry-formal-v1.json`, relative to research/rmaf, records a fresh source-bound replay in the local `replay/` directory. The compiler built copied sources of RMAF, Geometry, Bridge, Selector and Controls. The three imported source hashes match the frozen geometry certificate and current source bytes.

A Lean environment traversal audits every declaration whose module origin is one of those five modules, including definitions, generated proof declarations and explicit theorems. It inspected 759 declarations: RMAF199, Geometry128, Bridge162, Selector241 and Controls29. Their transitive axiom sets contain only propext, Classical.choice and Quot.sound. Selector contains59 explicit theorems and Controls22 literal theorems; these counts are not completion measures for the main algorithm.

Five false propositions were rejected specifically because kernel `decide` proved them false: shared T1 vertex has three regions, original root has an upward neighbor, suppressed display path is one original edge, side colors alone imply full mutual clearance, and an absent label passes the proper-input guard. The separate CustomAxiom module compiled, after which the same module-origin audit rejected all three affected declarations, including an entirely unreferenced custom axiom. Accepted sources contain no sorry, admit or native_decide.

The literal controls include exact T1 overlap vertices0,00,01 and both clear edges; the root-promoted six-label target; a genuine three-region selector; original unary paths; orientation; malformed and disjoint selections; identical and wrong rooted restrictions; and a false forest. `geometry_controls.py` additionally reused the dedicated completed X0 checker after matching all nine input/dependency/code freeze hashes. It reproduced T1's877 partitions,30 P-refinements and10 agreement partitions, with minima5/5 under P and under P with A retained. It also rejected the original-whole-B one-cut claim using all six source edges. These numerical checks are development reuse of that checker, with no new independent implementation claim. No profile-author/referee X0 code was imported in this phase.

The formal replay took18.22957495799983 seconds; the fixed numerical-control wrapper took0.003891040999405959 seconds. Logs and first failed elaborations remain local. The broad toolkit suite was not rerun because the toolkit was unchanged and this phase used scoped Lean and literal graph checks.

## Acceptance boundary

Self-grade: scoped G CLOSED-UNVERIFIED, author-checked pending fresh nonauthor semantic/source replay and the consuming algorithm's interface review. The geometry theorem assumes the original target and its proper original-label selections are supplied; it does not establish a reached-state history invariant. No exchange theorem, source-core coverage, cut charging, complete solver, smaller-base runtime or novelty claim follows from this delivery.
