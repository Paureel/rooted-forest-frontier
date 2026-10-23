# Pinned bridge target and scope

Target selected after frozen independent controls, before Lean construction: G1 from pure_bridge/FORMAL.md, Remaining graph proofs table: "The unsuppressed minimal embedding of a nonempty label subset is a `RootedRegion` under a label-preserving binary-address representation."

The graph-level strengthening to prove is: every finite nonempty connected vertex support in the binary-address graph admits a minimum-depth root, and the original vertex set with that root is a `PureBridge.RootedRegion`. Adjacency means appending/deleting exactly one Bool. Connectivity is given by finite graph walks; prefix convexity and ancestry are not assumptions. Therefore every minimal embedding represented as a finite connected subgraph is covered, regardless of degrees or root position.

May assume: Lean Std and the existing PureBridge theorem with its printed hypotheses; standard binary-address encoding (each rooted binary edge maps to one-bit extension). Must not assume: prefix convexity, ancestor location of the support root, degree-two exchange, source/target split transport, or any field of ExchangeSystem.

Alternative delivery: if full executable minimal-hull construction is unavailable, prove the graph-connected-support realization and state the remaining extraction/encoding link to each concrete executable oracle separately. That is a graph theorem, not an oracle semantic certificate.

Controls: existing frozen control 3 retains degree-two intermediate vertices; root/singleton/clique controls cover boundaries. Lean negative controls must reject omission of graph connectedness and omission of the minimum-depth condition. No faster bound, safe-cover result, novelty claim or resolution of the prior 2^q route is licensed.
