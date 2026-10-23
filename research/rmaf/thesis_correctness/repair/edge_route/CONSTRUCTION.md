# Original-edge construction

The narrowed universal AF theorem remains open. Lean checks the original-edge operation, its single-exchange cost, and graph connectivity statements under explicit hypotheses. The remaining obligation concerns rooted labelled restrictions and disjoint embeddings in F1; restored connectivity alone does not establish either property.

## Proved statements

`OriginalEdges.lean` defines normalization on a duplicate-free list of original edge IDs. It filters out every cut on the selected path and inserts the actual parent ID only when at least two cuts were removed and that parent exists. `normalize_mem` gives the exact membership equivalence. The file proves that every resulting ID is original, every selected path edge is uncut, required cuts off that path remain cut, output IDs remain duplicate-free, and the cut count cannot increase. At a root, the exact new count plus the number of removed cuts equals the old count.

The graph statements use an inductive finite walk whose steps carry the original edge ID and its incident vertices. They prove endpoint reconnection, survival of old walks that avoid the added parent cut, survival of every old walk in the root case, and confinement of the normalized corridor component when all its outgoing edges are required pendant cuts or the added parent cut. Explicit labelled anchor walks at the two endpoint roots join after normalization. No AF predicate occurs among these conclusions.

`RootedPaths.lean` uses a parent map with a strictly increasing natural-number rank. An edge's original ID is its child vertex. Two actual downward paths from a common ancestor define the selected corridor. The incoming edge of that ancestor has ID equal to the ancestor itself, and it is absent when the ancestor has no parent. The file proves that the incoming ID lies outside both downward arms, then proves endpoint connectivity under the exact root-safe normalization. These statements do not require an assumption that the parent exists.

The rank assumption excludes directed cycles. The common ancestor need not be lowest for the connectivity theorem; a consumer using the source's LCA path must supply downward arms with disjoint interiors. Binary branching, leaf labels, and AF compatibility are not silently inferred from the rank condition.

## Exact open graph obligation

Let T1 and T2 be finite rooted binary trees with the labelled unary-rho convention. Let Fi be yielded forests of Ti. Require that each component label set of F2 lies in one component of F1. Let a and c root identical labelled subtrees in F1 and F2, with a and c siblings in F1. Let E2 be a subset of E, both sets consisting of original F2 edge IDs. Require that yielding F2−E2 retains those entire endpoint subtrees as siblings and that yielding F2−E is an AF of F1 and F2. At each endpoint, require a labelled vertex connected to the endpoint in F2−E within its original descendant subtree; intact endpoint atoms are a sufficient stronger condition.

Define P to be the original a–c path, u its LCA, and N the root-safe cutset. The unresolved **labelled-restriction exchange** statement is the following: for every labelled component S of F2−N, the rooted restriction of F1 to L(S) is isomorphic to S after yielding; for distinct labelled components S and R, their minimal embeddings in F1 are vertex-disjoint. Component containment follows once the graph operation is shown to remain inside each original F2 component. Forest status in F2 follows from cutting its own edges. Thus these two assertions are the missing AF conditions, rather than additional arithmetic or edge-identity conditions.

Two structural obligations also remain explicit when instantiating the proved walk lemmas: derive the corridor boundary condition from the actual pendant cuts and endpoint subtrees, and show that the supplied anchor walks avoid the optional incoming edge. The source geometry strongly suggests both statements, but this route has not formalized them from a binary-tree definition. No Lean axiom or placeholder stands in for them.

If a consumer works in a suppressed forest, it must also prove that its selected edge maps to the stated original edge or original path segment. The current proofs operate on one fixed original parent graph. They do not equate two cutsets because the yielded partitions agree.

## Compound endpoint boundary

The parent's fixture was frozen in `compound-boundary-frozen.json` and independently replayed. With T1=`(((a,(c1,c2)),x),y)` and T2=`((a,(c1,c2)),(x,y))`, cutting `ea,ec1,ec2` gives an AF. The pair `(a,(c1,c2))` is common, and containment holds. The compound endpoint root has no labelled descendant left in its root component. Restoring `ea` gives the wrong upper rooted restriction. This refutes arbitrary-E normalization without the endpoint-fragment condition.

The earlier reached-state census restricts E to actual active edges, so contracted atoms remain intact. Its 5,584 root premises remain finite evidence for that stronger setting. Earlier structural counts were bounded and did not establish the arbitrary-compound formulation. The original receipts have not been revised into a universal result.

## Consumer trace

| Use | Original-edge construction | Required additional argument |
|---|---|---|
| Lemma 6.10 first exchange, printed pp.112–113 | Work with `C=E0∪B`, where B is the pair of pendant cuts, and remove **all** cuts of C on the a–c path. The parent of u exists because u has sibling x. The proved operation retains B and every off-path old cut. | AF preservation needs intact atoms or surviving endpoint fragments. Source `E3` is a selected subset of the E0 path cuts, so the source's literal partial-restoration set is not automatically the full-normalization result. |
| Lemma 6.10 second exchange, printed p.113 | After cutting B, use the pair `(x,u)` and its path, with the optional incoming edge of their common parent. If that parent is an unlabelled component root, the actual parent option is `none`; all path cuts are removed and no edge is invented. | The subtree rooted at u has the common a/c shape after the first full restoration. The x endpoint can be compound, so its fragment condition still needs justification. Relating the yielded forest to original IDs needs explicit edge transport; the local edges ex and eu are identifiable, but no general suppression theorem is supplied here. |
| Theorem 6.12 A2BC exchange, printed p.116 | Add both pendant cuts, then fully normalize the a–c path. Required pendant cuts remain. Single-exchange cost is proved; the parent separately checks the combined cardinality inequalities. | The source literal formula restores ec alone. An existential replacement using full normalization can have a different original cutset. AF preservation and endpoint-fragment premises must be supplied, including the swapped endpoint form for protected c. |

For partial restoration, `full_to_partial_inclusion` states the exact condition for the full result to be contained in a proposed partial target: any parent cut added by full normalization must also belong to that target. This condition matters when the partial set restores one path edge but the full set removes at least two and therefore adds the parent. An extra-cut AF preservation theorem would then be needed to use such inclusion; this route does not assume it without a graph proof.

A separate controlled example demonstrates the distinction. With T1=`(((a,c),x),y)`, T2=`((a,c),(x,y))`, and `E={ea,ec}`, both endpoints are intact labelled leaves and E yields an AF. Restoring only ea fails AF validation. Full normalization cuts the incoming edge of `{a,c}` and passes. E is nonoptimal, so this example does not refute Lemma 6.10 or 6.12 with their full hypotheses. It does refute an unconditional substitution of partial restoration for the proved full edge operation.

## Validation and scope

The two proof files contain 26 named scoped theorems. They compile with only `propext`, `Classical.choice`, and `Quot.sound` in their audited axiom dependencies; some use no axioms. Positive controls check exact original edge lists, duplicate-parent handling, corridor isolation, and a ranked parent-map root example. A deliberately false control that inserts a phantom root-parent edge is rejected by Lean. Failed development compilations are retained separately; their temporary elaborator `sorryAx` output is not evidence for any delivered theorem.

The construction is ready for fresh nonauthor review. The universal AF-preservation claim, source suppression transport, marked-state induction, global correctness, and runtime claims remain open. No sibling component-route work was read.
