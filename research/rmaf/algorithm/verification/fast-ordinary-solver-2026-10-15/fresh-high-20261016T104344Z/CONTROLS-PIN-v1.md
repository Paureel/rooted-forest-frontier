# Literal controls frozen before geometry construction/search

Notation: `L n` is leaf n and `(u,v)` is a node. Forest blocks are raw list blocks, not selected by an optimum oracle. Exact true/false evaluation is required, not approximate agreement.

1. Identical literal cherry T=S=(0,1), p=[], F=[[0,1]]: proper=true, cherry=true, agreement=true, cuts=[], pendant partition=[[0,1]], refinement=true.
2. T=((0,1),2), S=((0,2),1), p=[false], F=[[0],[1,2]]: proper=true, cherry=true, agreement=true, pendant partition=[[2],[0,1]], singleton 0=true, singleton 1=false, refinement=false. Removing the singleton-0 branch must fail.
3. Same T,S,p, F=[[1],[0,2]]: agreement=true, singleton 1=true, singleton 0=false, refinement=false. Removing the singleton-1 branch must fail.
4. Same T,S,p, F=[[0,1],[2]]: agreement=true, both singleton endpoint tests=false, refinement=true. Replacing the pendant partition by all singleton blocks must fail refinement.
5. T=((0,1),(2,3)), S=((0,(2,3)),1), p=[false], F=[[0,1],[2],[3]]: proper=true, agreement=true; pendant partition=[[2,3],[0,1]], refinement=true.
6. Same as 5 but F=[[0,1],[2,3]]: raw same-endpoint-block/multiple-pendant-label control, agreement=true, refinement=true.
7. Source/target swap of case 2: pendant partition from T is [[0,1,2]], different from the required S partition [[2],[0,1]]; the cherry premise in swapped S must fail. This detects the wrong source rather than claiming a counterexample to the literal implication.
8. Equal-label cherry T=S=(0,0), p=[], a=b=0: CherryAt=true but proper=false. No distinctness follows from CherryAt alone.
9. Improper mismatched labels T=(0,1), S=(0,2), F=[[0,1]]: proper=false and agreement=false.
10. Shape corruption case 2 with F=[[0,1,2]]: agreement=false.

All ten cases must be checked by fresh own Lean code using only the pinned program definitions. Kernel proofs by `decide`/`rfl` are preferred; Boolean refinement is accompanied by an own equivalence to literal `VertexGeometry.Refines` before it can carry the target's meaning.
