# Frozen controls and independent representation

Frozen 2026-10-14 before reading any pure-bridge candidate proof, implementation, or results. Expected answers below are hand-derived. The candidate supplied in the assignment is known; no claim of conceptual independence from that statement is made.

## Representation to implement

A rooted binary tree is an explicit vertex/parent adjacency structure, with unique leaf labels. The minimal embedding of a nonempty label set is the union of undirected simple paths from one chosen leaf to every other chosen leaf (singleton: its leaf vertex). This preserves unsuppressed degree-two vertices. The rooted restriction is independently encoded by recursively pruning absent labels and suppressing unary vertices. A forest refinement is a set partition; it is feasible when restrictions match blockwise and embeddings are vertex-disjoint in source and target, and avoid all marked target vertices. Cost is number of blocks minus one. All arithmetic is integer/exact.

This is purpose-specific verification code. The tools index and recipes contain no rooted agreement-forest/finite-tree verification engine; existing campaign oracles and pure_bridge/check_geometry.py must remain unread and unimported for this independent route. Therefore a small independent verifier is justified rather than a copy or wrapper of those engines.

## Hand controls

1. **Singleton/null**: tree leaf a, block {a}: embedding {a}; restriction a; optimum cuts 0. No marks is the identity.
2. **Root cut**: tree (a,b), mark its root: one block is forbidden, singleton partition is feasible, optimum cuts 1. Root degree is 2, not 3; the mark creates 2 nonempty regions.
3. **Crossing paths / suppressed vertices**: T=((a,b),(c,d)); A={a,c}, B={b,d}. Each hull contains root, left-cherry root, right-cherry root; their intersection has exactly those 3 vertices. Every intersection vertex has degree 2 within each hull. Both root(A) and root(B) are the target root. The unrefined blocks conflict. Splitting B at the target root yields {b},{d}, which avoids A at additional cost 1.
4. **Degree-three negative**: T=(((a,b),c),d); A={a,c,d}, B={b}. B is a singleton leaf, so the hulls are disjoint. Replacing B by {b,d} and A by {a,c} removes leaf-disjointness and must be rejected as a forest partition rather than accepted as a pure instance. Separately, T=(((a,b),c),(d,e)); A={a,c,d}, B={b,e} have a shared degree-3 vertex in A and must fail the pure-degree-two test.
5. **Multiple marks and empty region**: T=(((a,b),c),d), mark target root and its child subtending {a,b,c}. Three nonempty leaf regions remain: {a,b}, {c}, {d}; the isolated root-side empty region contributes 0. For identical source T, optimum marked cuts=2, r=3, residual q=0.
6. **Old-mark preservation**: T=((a,b),(c,d)); mark left-cherry root. B={b,d} is initially forbidden. Every feasible refinement avoids that mark; splitting any one of its blocks further cannot introduce the old mark.
7. **Topology disagreement**: source ((a,b),c), target ((a,c),b): optimum ordinary cuts 1 (two blocks); whole block fails equal restrictions; every two-label block has the same rooted cherry shape.
8. **Three-way clique**: T=(((a,b),c),((d,e),f)); blocks {a,d},{b,e},{c,f}. All 3 contain the target root; all overlap vertices have degree 2 in both hulls. At most one block can remain uncut; minimum global added cuts 2. Tie choices of deepest root must all be exercised.

## Frozen detectors and negative plants

- Compare every expected control field exactly; change its integer answer by +1 and require rejection for each numeric field.
- Replace unsuppressed hull with its suppressed restriction vertices on control 3: detector must reject the missing left/right path vertices.
- Delete old marks during a split: a deliberately marked occupied block must fail feasibility.
- Count empty components of a vertex-deleted graph as target regions: control 5 must reject the resulting r=4.
- Treat overlap degree <=3 as pure: control 4 degree-three instance must be rejected by the correct predicate.
- Treat leaf overlap as permitted: control 4 nonpartition must be rejected.
- A deliberately false Lean theorem about root splitting must fail kernel elaboration; production proof contains no sorry, custom axioms, or native_decide.

## Gate and alternatives

Pilot the controls first and retain timings. Then a bounded exhaustive/sampled adversary run may test actual tree/partition interfaces. A finite no-fire is not a universal proof. An in-regime counterexample refutes its exact statement; an out-of-regime witness only diagnoses a missing hypothesis. Main deliverable may be a narrower formally checked bridge with all missing links named. General faster bound, safe cover, novelty and prior 2^q audit remain OPEN.
