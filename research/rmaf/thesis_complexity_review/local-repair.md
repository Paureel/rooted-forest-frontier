# Two-active-leaf local repair

This is a new local argument written after the independent audit. Its grade is **proposed proof, not yet fresh-author verified**. It does not settle G4 with three or four active leaves, the cardinality-three state, or Theorem6.13.

## Precise joint obligation

Let J be a reachable G4.1 invocation with cut budget K, P={a}, Q=∅, and three pendant nodes. Write A,B,C for its three legal children. Under the source's appropriate induction hypotheses, the needed conclusion is

`1 + I(A) + I(B) + I(C) ≤ α 2^(K−1) − 2`.

The stated independent child estimates are respectively `α2^(K−2)−2`, `α2^(K−3)−3`, and `3α2^(K−4)−1`. Their sum plus one is too large by `α2^(K−4)−3`. The sufficient repaired estimate is `I(C) ≤ α2^(K−3)−1`. This suffices algebraically, but needs a structural proof on the actual descendant calls. An enlarged abstract domain alone cannot prove it.

## Local geometric lemma

Assume J's remaining local F1 subtree is `(a,(x,y))`, with a and x,y active roots. In F2:

1. a has a sibling subtree b, and the incoming edges of both a and b are protected;
2. x,y are in one component, are unprotected, and have exactly three pendant nodes;
3. x is at least as deep as y;
4. all three A3BC branches of J are legal (in particular, cutting every pendant edge is legal), and earlier cases have been considered first.

In J's C-child, y is cut and x becomes protected. Then either no branch is legal, or the only legal branch cuts at least two pendant edges. In fact, the live case here has at least three pendant edges.

**Proof.** If x is outside b, the edge to b remains a pendant edge on the a–x path whenever a and x are connected. It cannot be cut because it is protected. The endpoints a and x are protected as well. If they are disconnected, AC's two endpoint cuts are both forbidden. Hence no branch is legal in this case.

Suppose x lies in b. Then y also lies in b. Otherwise the x–y path has a as a pendant node, contradicting the legality of J's B-child. Put r=LCA(x,y), and let h_x and h_y be the respective distances to r. Since the path has three pendant nodes, `h_x+h_y−2=3`. Since x is deeper, `h_x≥h_y`, so `h_x≥3`. If h_y=1, cutting y suppresses r; in that case h_x=4, and x remains at distance at least three from the root of the surviving b subtree. If h_y≥2, r survives and x remains at distance at least h_x≥3 from that root. Thus the a–x path after the cut has at least three pendant nodes. No endpoint cut is legal. B does not apply with a single pendant; RB/RB* endpoint cuts are forbidden; BCY's endpoint-containing branch is forbidden; 2B cannot apply with three or more pendants. The only possible legal branch cuts all pendants. This proves the claim.

The trivial reductions cannot bypass this argument: a and x cannot be a common cherry because their path has protected pendant b or at least three pendants. Neither becomes a component root from cutting y. In the inside-b case a remains outside the surviving b; in the outside-b case cutting away the protected sibling of a would be required, and the root-sibling exclusion prevents that operation.

## Connection to the source history

G1's A2BC C-child protects a and its F2 sibling b1 (p107). As long as a stays an active root and the source carries its credit to this G4 invocation, subsequent cuts cannot cut a or b1. Cuts inside b1 can suppress vertices, but the surviving edge inherits protection (p107). Therefore a continues to have a protected sibling subtree b. A common-cherry reduction involving a does not occur while its F1 sibling e has at least two active leaves. This explains hypothesis1 from the retained source history rather than assuming an arbitrary credit-count state has it.

This local lemma concerns the case where e has **two active leaves when J branches**. After y is cut, the next nontrivial pair is (a,x), so C has the structure just proved. With three or four active leaves in e, additional pairs are processed before (a,x), and the same conclusion cannot simply be imported.

## Conditional recurrence consequence

Take α large enough for the source's base cases (α≥128 suffices for the displayed p117 representative base bound). If K=0, C immediately fails on negative budget, so I(C)=1≤α2^(K−3)−1. If K≥1 and C has a child, the lemma gives a sole child with budget at most K−3 and with empty analysis credits after G5. Under the empty-credit induction bound, `I(C) ≤ 1 + (α2^(K−3)−3) = α2^(K−3)−2`. If it has no child, I(C)=1 is again covered. Thus the sufficient repair holds for this two-active-leaf case.

Using the source A/B estimates then gives `1+I(A)+I(B)+I(C) ≤ α2^(K−1)−5`, which is below the parent bound. `RepairArithmetic.lean` checks this conditional affine implication universally; it does not formalize the geometric lemma.

## Remaining proof debt

For e with three or four active leaves, the C-child first processes remaining local sibling pairs. A valid repair must bound those descendants jointly while retaining the protected-sibling history, and explicitly handle the demonstrated three-credit state. Neither the nine-leaf dead end nor a larger finite timing census supplies that theorem.
