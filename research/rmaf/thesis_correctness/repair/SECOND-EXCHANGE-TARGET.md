# Specific second-exchange transport, version2 target

This is a new continuation after the first two construction reports. Preserve those reports and receipts. The in-flight fresh reviewer is reviewing the earlier frozen construction; do not steer that review or claim its verdict covers this continuation.

Own new files only in `repair/edge_route/second_exchange_v2/`, plus `results/thesis-correctness-repair-edge-second-*` and the already-owned edge-route progress record. Read this target first and immediately write a skeleton. Adversary before proof. Use existing independently written edge-route checker after its fixed controls; record reuse explicitly. No component-route code imports.

## Candidate lemma

Let F be a reduced finite rooted binary forest with labelled unary rho roots as applicable. Let a,c root nonempty disjoint descendant subtrees, u=LCA(a,c), and let x be the original sibling of u, with common parent v. Let P be the original a–c path. Let B be exactly the two incoming edges of all pendant subtrees off the internal vertices of P. Thus none of B lies inside endpoint subtrees or x. Let G=yield(F−B).

Candidate structural facts: x,u,v survive yielding; ex and eu are the same original edges with the same endpoints in G; the incoming edge of v, if present, also survives unchanged, and absence of that edge is preserved. The only original non-B edges altered by suppression lie on P. Hence every original edge outside B∪P survives with its original ID and endpoints.

Let K be any original-edge cutset with B⊆K and K∩P=empty. Put C=K\B. Candidate transport: C consists of unchanged actual G edges; yielding G−C equals yielding F−K as a labelled rooted forest, with the correspondence fixing surviving x,u,v. Root-connected label fragments at x,u agree. Exact count: |K|=2+|C|. This transports the first full-normalization output, since full normalization removes every cut on P and its optional parent edge eu is outside P.

The second x–u path in G is exactly {ex,eu}. Root-safe normalization on that path uses the original optional incoming edge of v. Show that its normalized residual cutset C' lifts literally to K'=B∪C', retaining B, the same yielded forest and root fragments, and exact count2+|C'|. This is specific geometry transport, not a general suppression/contraction theorem.

## Assumptions and limits

May assume finite reduced binary validity, actual original parent edges, nonempty endpoint/x subtrees and the stated exact pendant geometry. May reuse already proved list/walk lemmas with exact hypotheses. May NOT assume yield/cut commutation, cost-preserving suppression transport, AF normalization, a global marked-state invariant or the candidate structural facts. If any are false, retain the smallest exact counterexample. Component AF preservation remains a separate source; do not silently import its pending prose proof.

## Frozen concrete controls

Read `repair/two-stage-original-spec.json` as input data only. Independently reproduce optimum2 and both original cutsets {ea,ec}, {ea,ex}, with counts2→3→2 and final pendant pair. Both forests must be actual AFs. Independently check actual yielding G and the ID/endpoints correspondence above, not just equality of partitions. Corrupt the map by retaining a suppressed corridor edge as an unchanged edge; it must fail. Test a detached-rho component-root variant to check absent incoming edge of v. Then bounded reached2B states may challenge the lemma, with a measured pilot and honest denominator.

## Delivery

A precise proof of this geometry-specific transport, meaningful Lean local structure if feasible, or a smaller explicit open lemma with exact counterexample/search evidence. Preserve new source/proof hashes. Do not modify the first construction or ask the in-flight reviewer to accept new artifacts. Report to parent for a later fresh verification pass.
