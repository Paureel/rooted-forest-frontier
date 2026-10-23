# Source-boundary controls frozen before further proof

The v3 resource guard is qualified by all ten declared tiny controls in `GUARD-QUALIFICATION-v3.json`, using guard SHA256 `97d512008b4ce66734c204565cfbfde31b4d8437ff378e1c6837e48581604200`. The two earlier guard qualifications remain refused; no Lean proof was run during guard development. Process inspection requires the permitted escalation because the default sandbox blocks child `sysctl` calls.

Use literal trees, raw forests and the exact inherited definitions. `L n` denotes a leaf and `(u,v)` denotes a node. These values are development controls in a continuation, not a fresh independent acceptance route.

Positive controls:

1. S=(0,1), a=0,b=1,F=[[0,1]],P=[0,1]. Source labels are distinct, partition and embedding checks are true, the restriction is S with a root cherry, cuts=[], and NoPendantCrossing is true.
2. S=((0,2),1), F=[[0,1],[2]], P=[0,1]. All source-boundary premises are true; the restriction is (0,1), the pendant partition is [[2],[0,1]], and NoPendantCrossing is true.
3. S=(((0,2),3),1), F=[[0,1],[2],[3]], P=[0,1]. All premises are true; cuts have length two, pendant partition=[[2],[3],[0,1]], and NoPendantCrossing is true.
4. S=((0,(2,3)),1), F=[[0,1],[2,3]], P=[0,1]. All premises are true; pendant partition=[[2,3],[0,1]] and NoPendantCrossing is true.
5. S=(((0,2),1),3), F=[[0,1,3],[2]], P=[0,1,3]. All premises are true; the restricted source is ((0,1),3), with cherry at [false]. The core legitimately contains upward label 3. Pendant partition=[[2],[0,1,3]], and NoPendantCrossing is true.

False/corrupted controls:

6. Remove the restricted-cherry premise in case 2 and use F=[[0,1,2]],P=[0,1,2]. The source partition and embedding checks remain true. NoPendantCrossing is false, witnessed by pendant label 2 and core label 0 in the same block. The source restriction has no cherry with endpoints 0,1.
7. Remove disjoint embeddings in case 3 and use F=[[0,1],[2,3]],P=[0,1]. Partition and the restricted cherry remain true. pairwiseEmbeddings=false and NoPendantCrossing=false, witnessed by 2 and 3 in a crossing block.
8. Replace case 2's pendant partition by [[0],[1],[2]]: refinement of F is false. Swapping the source with T=((0,1),2) produces partition [[0,1,2]], different from [[2],[0,1]].
9. Equal labels S=(0,0),a=b=0: source Nodup=false and a!=b=false, while the literal CherryAt predicate at [] is true. These failed premises must be visible.
10. Improper S=((0,2),(0,1)): source Nodup=false. No source-boundary conclusion may be certified from the required premises.

Recheck the inherited original-target singleton endpoint controls: T=((0,1),2),S=((0,2),1),F=[[0],[1,2]] and F=[[1],[0,2]] are valid agreements with pendant refinement false. Omitting the respective singleton branch must be rejected. The inherited four universal components must be recompiled through the qualified guard before reuse.

Expected false propositions will be submitted as deliberately false kernel proof goals and must be rejected. Finite controls do not prove the source-boundary statement or HighRule coverage.
