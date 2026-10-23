# Root-sibling extension target

Pinned before its X0 test and construction. This makes the later protection consumer explicit without changing the earlier pins.

Let G be a reduced labelled forest and r an unlabelled component root with outgoing edges e1,e2. For every additional raw current-edge set D disjoint from {e1,e2}, target **RS_all** is

`yield(G-(D union {e1})) = yield(G-(D union {e2}))`.

Also target **RS_double** is equality of this yield with `yield(G-(D union {e1,e2}))`. Counts differ: the double set has exactly one extra cut. Thus any minimum cutset for a yield-invariant acceptance predicate cannot include both root edges, provided deleting either one leaves an actual accepted set. These are claims to establish, not assumptions. They cover additional internal cuts that empty a child subtree.

For a minimum residual cutset R containing e2, the protection consumer must either show that e1 in R gives a removable redundant cut, or replace e2 by e1 with unchanged size/yield before choosing the protected origin on P_e1 in the original graph. Selecting an origin on P_e2 does not address a protected sibling on P_e1.

Exact additional control using controls.json base_graph: first cut C={er}, so r is an unlabelled root. Let D={eb,ec}, e1=ea and e2=es in G. Cutting D union {ea}, D union {es}, or D union {ea,es} yields four singleton labels rho,a,b,c. Their residual raw cut counts are 3,3,4 respectively. The first two have equal topology despite a now-empty child fragment. The false rule that double cutting keeps cardinality three must be rejected. Supplementary X0 must test arbitrary D, not infer this claim from the previously pinned single-cut controls.
