# Source and hypothesis ledger

Source: Chris Whidden, July 2013 thesis, local PDF `research/rmaf/sources/baseline/whidden-thesis-2013.pdf`; text is its local extraction. Printed page = PDF page minus 13. No external source or bibliography entry is added.

## Read / retrieved

- Ch2 p12 (PDF25): "we augment the tree with a labelled root node" whose only child is the old root. Convention here: labelled unary rho is retained, counted separately from active leaf labels. Unlabelled nodes with fewer than two children are suppressed; rho is not silently deleted.
- Ch2 p15 (PDF28): yielded forest suppresses unlabelled nodes with fewer than two children. Cut all specified edges in the original forest before suppressing; protection inheritance is OR along surviving paths. This does not assert an arbitrary deleted forest is algorithm-reachable.
- p104–105: shared F1/F2 subtrees form roots-todo units. Root removal and common sibling merge are local processing steps.
- p107: branch admissibility excludes protected cut edges and root-incident edges with protected siblings. "If at least one of e1 and e2 is protected in F2, then e inherits this protection". A2BC with protected c uses B then A, adding pendant protection in A; ordinary A2BC uses A,B,C, protects a and both pendant edges in C.
- p109: A3BC has costs 1,s,1 and protects the retained a endpoint in C. Earlier RB, RB*,2B,BCY cases have priority.
- p110, rendered afresh as source-p110.png: depth-rule eligibility is under the deepest top endpoint of a protected F1 edge, then maximal F1 depth, then preference for separated F2 components or deeper F2 member. BCY's two cuts cost s and 2. Orientation puts the deeper F2 endpoint first (explicitly used in source p121).
- p111 Fig6.5: failure k<0 precedes success |Rt|≤2; common merge and root-removal return to Step2, without another recursive invocation. Final Step7 says SC although surrounding definition is AC; this route treats it as the separate-components case, not a new branch.
- p117: source declares P has up to two nodes, Q⊆P; calls counted include the invocation itself, evidenced by all recurrences `1+...`. Source induction assumes empty-credit bounds at every smaller budget, with intermediate groups justified backwards, not an arbitrary all-state induction. Source negative-budget convention -3≤k<0 accompanies capped effective branch costs.
- p118, rendered afresh as source-p118.png: G1–G6 decomposition; initial A3BC C gets P={a},Q={a}; G2 common sibling merge moves to G3 within the same invocation.
- p119–121: G2 and G3 local retention/discharge and double-protected pair transitions. Their structural arguments are read, not imported as formal theorems.
- p122–123: G4 subtree has at most four active Rt units under source depth argument; lifted G1–G3 credit assignments plus exceptions. Exact p123 exception: G4.1 A3BC A retains incoming P,Q; B empties both; C adjoins a' to both. Case2B empties both.
- p123–126: G5 pair and potential sibling-merge cases; source discharge argument distinguishes a' at depth one/two. No assertion that these arguments cover reachable p=3 state is imported.

## Inferred / proposed here

The generic affine certificate, finite credit-domain arithmetic, and all recurrence repairs are derived here, checked below; they are not assertions attributed to the thesis. A finite branch/cut replay is a control only. The minimal extra structural premise will name a continuation frontier and its coefficient/intercept directly; existence of that frontier for every source-reachable G4.1 state is OPEN.

## Forbidden imports excluded

No geometric-arm material, adversary implementation/proof, parent implementations, or correctness/transfer work was read or imported. No arbitrary transition closure, p≤2 cap, protection-persistence lemma for arbitrary cuts, or desired C-child estimate is assumed.
