# Control pin v1, 2026-10-14

Frozen before execution or general proof construction. Exact Lean `decide` on the actual RMAF definitions is the production checker. Positive propositions must elaborate; each negative twin must fail specifically because `decide` found the proposition false. A separate malformed identifier is diagnostic only. No tolerances.

1. Swapped root: t=node(0,1), u=node(1,0), B=[0,1]. Restriction agrees; singleton supports are disjoint in both. Their leaf-0 addresses differ ([false] versus [true]). Root degree is two. False twins assert identical cross-tree supports and degree three.
2. Suppressed path: t=node(node(0,1),2), u=node(2,node(1,0)), B=[0,2]. Exact t support=[[],[false],[false,false],[true]]. t leaf-0 singleton=[ [false,false] ]. False twins omit [false] or include root in singleton.
3. Different outside labels: t=node(node(0,7),2), u=node(2,node(8,0)), B=[0,2]. Restrictions agree; [0]|[2] agrees and is disjoint in both despite unequal global leaves.
4. Overlap: t=u=node(node(0,1),node(2,3)); [0,2] and [1,3] each agree but their embeddings overlap. False twin asserts disjointness. Positive twin [0,1]|[2,3] is disjoint.
5. Global cost: same four-leaf tree, original [[0,2],[1],[3]] and replacement [[0],[2],[1],[3]] both agree, lengths 3 and 4. False twin asserts unchanged cost.
6. Null/malformed regime: empty and absent selections have empty supports; singleton has one vertex; repeated leaf labels fail Nodup. False semantic twin claims repeated labels are unique. Unknown Lean identifier is an independent diagnostics-only control.

Independence: expected values above are hand constructions from tree paths, frozen before execution. We share the actual executable definitions with other routes (the deliberate target), but no graph-route or parent split code, proof derivation, checker or output has been read. These controls are author checks, not fresh-review certification.
