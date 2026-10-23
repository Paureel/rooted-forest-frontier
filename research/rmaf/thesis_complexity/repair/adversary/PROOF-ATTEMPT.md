# Independent adversary proof attempt

Grade: NO-FIRE on the stated two-active-leaf geometric claim; ordinary mathematical argument below, not a formally verified tree theorem. The source-history import needs the prescribed-cut-shape premise made explicit. No result here closes the global runtime theorem, the three/four-active-leaf G4 case, or the reachable three-credit state.

## Premises used, exactly

J is a source invocation after trivial processing, under the labelled unary-rho convention. Its relevant F1 fringe is `(a,(x,y))`, where a,x,y denote distinct active roots (each could represent an already contracted common subtree). The incoming F1 edge of a is protected. In F2, a has sibling subtree b and both incoming edges are protected. x,y are connected, unprotected, and have three pendant nodes; x is no shallower than y. J actually selects (x,y), respects the source's earlier-case priority, and all A3BC branches are legal. Its C-child cuts y and protects x in F1,F2. No two-credit cap is assumed. A success/failure return is a childless invocation with count one. Counts refer to the full legal recursive-call tree.

For the conditional recurrence only: valid smaller-budget empty-credit induction bounds and the specified A/B allowances are imports. They are neither derived from the finite census nor certified by it. Alpha is chosen to cover source base cases (the displayed alpha>=128 choice suffices for the elementary dead-C bound). Analysis credits do not determine protected-edge sets.

## Geometric proof attempt

1. Suppose x is outside b. Cutting y cannot erase b: if y=b, the C cut is forbidden because b is protected; if y is strictly inside b, deleting its single incoming edge leaves its sibling side, and protection is inherited through any suppression. If y is outside b it leaves b intact. Thus a keeps a protected sibling after C. If a,x are connected, their path has the surviving b as a protected pendant. If disconnected, AC can only cut a or x. Both endpoint incoming edges are protected. A branch cutting all pendants is also forbidden in the connected case.

2. Suppose x is inside b. Then y is also inside b: otherwise the a incoming edge is pendant to the x–y path and the proposed B-child of J is illegal. This uses that a,x,y are distinct active roots, hence neither x nor y lies below active a.

3. Put r=LCA(x,y), hx=distance(r,x), hy=distance(r,y). Binary active-root geometry gives hx+hy-2=3. Depth orientation gives hx>=hy. Hence hx>=3. If hy=1, then hx=4 and cutting y suppresses r, shortening the surviving root-of-b to x path by at most one; its length remains at least three. If hy>=2, the suppressed parent of y is strictly below r, so the r–x path is unchanged and still has length at least three. The a–x path therefore has at least three pendants after C. The natural-number inequalities are Lean checked; the mapping from a source tree to these distances is not formalized here.

4. The next nontrivial pair in C is (a,x). Removing the detached active y from F1 leaves the cherry (a,x). Because a and x both have protected F1 incoming edges, the deepest protection top is their parent; the source depth eligibility rule excludes pairs outside this fringe. Neither endpoint becomes an F2 root by this y cut. The two endpoints cannot merge as a common cherry: in case 1 there is a protected pendant or separate components, and in case 2 there are at least three pendants. The source's immediate success test can terminate the invocation, which is harmless for a child-count upper bound.

5. Every source case is now accounted for. AC, RB, and RB* cut protected endpoints and make no legal call. B and 2B do not apply in the live inside-b case because there are at least three pendants. BCY's endpoint-containing cut is illegal; only its all-pendants branch can survive. A2BC cannot apply in the live case; A3BC has only its all-pendants branch legal. In the outside-b case the protected pendant defeats any all-pendants branch, and all other branches contain a protected endpoint. Thus C has no child, or exactly one child cutting at least three pendant edges.

This establishes the proposed geometric implication as an ordinary mathematical proof attempt. The earlier source predicates can remove a would-be all-pendants call; they cannot create a cheaper legal call once both endpoints are protected.

## Protected-sibling history: the precise extra reasoning

G1 A2BC C protects the incoming edges of a and its sibling b. While a remains an active root, a common-cherry contraction elsewhere cannot remove a's parent or its sibling relation. F1 singleton-component reductions do not change F2. Every cut operation still needs to preserve at least one active descendant of b. The sentence “the edge is protected, so it survives” alone is insufficient for arbitrary simultaneous cuts: the retained exact witness `thesis-runtime-repair-adversary-history-premise.json` cuts both children x,y of protected b=(x,y), erasing b without cutting its incoming edge. This is OUTSIDE the prescribed source branching regime and is not a counterexample to the local repair.

For source branches, total erasure is excluded by their shapes:

* A singleton cut cannot erase protected b. A cut equal to b is forbidden. A proper cut inside binary b leaves the other side, whose new incoming edge inherits protection. A cut above b also contains a and preserves their sibling relation in a detached component.
* A set of all pendant edges of an endpoint path cannot erase b. If the path enters b, an endpoint/path segment inside b survives. If the path does not enter b, b is either untouched, is inside a detached pendant component together with a, or is itself a pendant whose cut is forbidden. This uses the unique-path structure, not edge protection by itself.
* BCY cuts c and y, where y is the sibling of its protected uncle x. If y lies properly inside b, its sibling x remains inside b unless c=x; that equality is illegal because x is protected. If y=b, its cut is illegal. The remaining placement cases leave b untouched or keep it with a in a detached component. The c cut alone cannot erase b unless c=b, also illegal.

These cases cover AC, B, RB, RB*, 2B, BCY, A2BC, A3BC. They give a plausible complete history proof under the explicit invariant that a is still an active root. They have not been formalized as an exhaustive source-state theorem. The smallest remaining structural formalization gap is the path-pendant and BCY placement exhaustion, plus the source assertion that the carried a credit always denotes that unmerged active root until this G4 use-site. No finite singleton census fills this gap.

## Conditional descendant arithmetic

If J has budget K, C has budget K-1. A live C spends at least another three, so its child has budget at most K-4 (slightly stronger than the proposed text's K-3). Under the smaller-budget empty-credit induction bound, and where that bound is applicable, this yields I(C)<=alpha*2^(K-4)-2, hence the proposed sufficient alpha*2^(K-3)-1 bound. If the post-cut budget is negative, the child is an immediate failure and is handled by the explicit base bound instead. For K=0, C already has negative budget and I(C)=1. For every K>=0 and alpha>=128, the sufficient RHS is at least 15 and therefore covers a childless C. G5 resets credits on its sole legal call by source p126; the actual protected edges remain.

Taking only the weaker sufficient C allowance, the three allowances plus the parent are
`1+(4M-2)+(2M-3)+(2M-1)=8M-5`, where M=alpha*2^(K-4). The parent target is 8M-2. The exact rational coefficients and their positive-denominator integer form were executed; the latter and the universally scaled affine implication are Lean checked in `AdversaryArithmetic.lean`. The original independent allowances have coefficient 9/16, not 1/2.

## Scope of the no-fire result

20,000 random 6–8-active-leaf local trees yielded 2,491 admissible J orientations, 3,391 C orientations (including depth ties), 267 live and 3,124 dead outcomes, and 156,602 singleton-history checks. No tested admissible C had a legal branch cutting fewer than three edges or a legal branch other than all-pendants. This is finite screening only. The positive live fixture is locally admissible; this arm does not claim it has a full unprotected-root source history with Q empty. The nine/thirteen-leaf certificates were replayed branch-by-branch with fresh graph code and full-call-tree eligibility; no claim is made about short-circuit visits.

The sufficient C estimate survives the attack in its stated two-active-leaf scope. Extending it to three/four active leaves would require new premises and is not licensed by this report. The three-credit control remains a live obstacle to the source's stated cap, independently of this local repair.
