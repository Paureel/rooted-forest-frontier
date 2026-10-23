# Geometric repair candidate, with formalization boundary

**Status: conditional mathematical argument, not independently reviewed or fully formalized.** The Lean file checks the surviving-descendant kernel and every affine composition below. It does not yet encode the source trees, rule priority, depth eligibility, or the reduction from source rules to the kernel. Accordingly this file does not certify Theorem 6.13 or a universal runtime bound.

## Statement and explicit hypotheses

Let J be the first three-child invocation in its current G4 analysis block. Its active F1 region is `(a,((x,y),z))` (three active roots in e) or `(a,((x,y),(u,v)))` (four roots). Suppose J uses A3BC on the oriented pair (x,y), has exactly three pendant edges, and all A/B/C branches are legal. Let its budget be K and C's budget k=K-1. Assume:

H1. In F2, a is an active root with protected incoming edge and protected incoming edge of its sibling subtree b. The two endpoints are protected separately; neither assertion is a statement about analysis credits.

H2. The active root x is outside b. The original source history at G1 had a,c and x,y at the same F1 depth, x and y were already active there as an eligible sibling pair, and the depth rule chose (a,c). This is a sufficient history certificate for H2, using the preservation argument below. For an arbitrary locally protected state, H2 must be checked and cannot be dropped.

H3. The source rules, their priority, active-root reductions, orientation (deeper member first), and depth/tie selection apply literally. In the four-root case, the pair (u,v) is eligible at J and has the same F1 depth as (x,y).

H4. For every frontier invocation with empty analysis credits at a smaller budget h, the source induction hypothesis is available verbatim: `I(h,empty,empty) <= alpha * 2^h - 3`. The count includes the invocation itself. Use alpha>=128 and the unary labelled-rho convention. No credit-cardinality cap is assumed.

The candidate conclusion is `I(C) <= alpha * 2^(K-3) - 1`. Here the frontier can be taken after the local region has collapsed and the final (a,e) branch has been processed. Resetting the analysis credits at this frontier must be stated explicitly in a repair, rather than inherited from the false two-credit-cap declaration.

**Remaining formal premise:** the rule-specific geometry in Lemmas 1–5 below is ordinary mathematical reasoning. It needs independent adversarial proof review and a source-tree formalization before this conditional candidate can be promoted. In particular, the source-to-frontier credit reset is a proposed analysis amendment and is not a fact about the frozen original annotation algorithm.

## Lemma 1: source cut sets cannot erase a protected sibling

Each legal source cut set cuts at most one child edge of any binary vertex.

* Singleton cut sets have this property immediately.
* All-pendant cut sets consist of off-path edges attached to the simple path between two distinct active roots. Every internal path vertex has exactly two path-incident edges and at most one off-path child edge. A vertex outside the path contributes no outgoing cut edge. The active endpoints contribute none. Thus two sibling edges cannot both occur.
* BCY's compound set is {e_c,e_y}, where y is sibling to the protected active uncle x. If c and y had the same parent, c=x. But c belongs to the selected F1 cherry and x is its uncle, so they are distinct active roots. Thus these two cut edges are not siblings either.

Now consider an uncut protected incoming edge to a nonempty binary subtree b. A retained leaf trivially survives. At an internal vertex at least one child edge is uncut; recursively follow such an edge. Finite descent reaches a surviving leaf. This induction is precisely `surviving_descendant` in Geometry.lean, with the no-sibling-cuts hypothesis exposed. Suppression propagates the original protection by logical OR, as specified on source p107. Therefore b may shrink but its surviving incoming edge remains protected.

If a remains an active root, its incoming protected edge cannot be cut. Neither b nor a can disappear in a legal source cut. The pair persists as a with a protected sibling subtree, even if their common ancestor becomes a component root; the additional root-sibling exclusion on p107 is retained. While e has at least two active roots, a is not in an F1 cherry with e and cannot merge away.

**Failed strengthening retained:** arbitrary simultaneous deletions do not preserve b. In `(a,(p,q))`, protecting a and b=(p,q) while cutting p and q erases b. The Python control and Lean negative control catch this. There is no unrestricted-deletion lemma in this argument.

## Lemma 2: the original depth history places x outside b

At G1, x,y and a,c have equal F1 depth. The source tie rule chooses a,c with a at least as deep as c in F2. If x were a strict descendant of a's sibling b, x would be deeper than a in F2. Therefore (x,y) would outrank (a,c), contrary to the source choice. If x=b, its incoming edge becomes protected at the G1 A2BC C branch and cannot support J's legal A branch cutting x. So x is outside the original b.

Lemma 1 keeps a and the surviving b paired while a is active. Cuts never move an active root into b. A common-cherry contraction cannot merge an outside active root with an inside root while a is retained: the a edge is a protected off-path edge on their connecting path. Thus x remains outside the surviving b.

For a three/four-root e in the Figure 6.6 geometry, x and y at distance two below e are original active roots at the same depth as a. A current root at that distance could not have arisen by merging a deeper pair, because the original local subtree has height at most two. This is where the original depth history is used. It is not replaced by the number of current credits.

## Lemma 3: terminal barrier and a two-root local estimate

Once e has collapsed to one active root d containing x, d stays outside b. If a and d are connected, b is a protected pendant subtree of the a–d path. If they are disconnected, the rule is AC. In either case a cannot be cut and an all-pendant cut cannot be used. Any possible continuation cuts d (one or more edges in an earlier compound rule can only improve the bound). A common merger a,d is impossible. Thus at this terminal local pair there is at most one child with budget reduced by at least one.

Consider instead the F1 region `(a,(x,z))`, with x protected, outside b, and (x,z) nontrivial. Cutting z leads to the blocked pair (a,x), which has no legal branch: both endpoints and the b pendant are protected (or the endpoints are disconnected). Cutting x is forbidden. A legal all-pendant branch merges x,z, then reaches the terminal barrier and spends one more cut before the frontier. If the x–z path has one pendant edge, B is the sole branch and the cost to the frontier is two. If it has at least two, the endpoint branch contributes only a dead invocation, and the all-pendant route spends at least three cuts in total.

Rule priority does not add an extra branch here. RB/RB* either attempt the forbidden x cut or take the dead z route. 2B makes its single two-edge cut. BCY has uncle a, so its compound branch would cut z and a's protected sibling b and is illegal. AC has only the dead z route.

At budget h, writing E for the empty-credit frontier bound, the worst two forms are:

* one pendant: `1 + (1 + E(h-2)) <= alpha*2^(h-2)-1`;
* at least two: `1 + 1 + (1 + E(h-3)) <= alpha*2^(h-2)-1`, provided `alpha*2^h >= 8`.

These are `e2_one_pendant` and `e2_two_or_more`. If the pair is already a common cherry, permit a free merge and use the weaker bound `1 + E(h-1) = alpha*2^(h-1)-2` from the terminal barrier. This free-merge alternative must not be silently given the stronger bound.

## Lemma 4: three roots in e

After J's C cut removes y, the region is `(a,(x,z))`. The pair x,z cannot be a common cherry created by cutting y. If x and z were already siblings, J would have used RB with uncle z. If suppressing y's parent creates that cherry, either x,y were already siblings (contrary to J being nontrivial), or z was y's sibling and J would again have used RB. Root-trivial z only leaves the blocked pair a,x. Thus the strong two-root estimate of Lemma 3 applies, giving the target C allowance.

## Lemma 5: four roots in e, including three credits

After J's C cut, the region is `(a,(x,(u,v)))`. Both u and v are distinct from y. They cannot be in different components: if they had been in different components at J, the source's tie rule would have chosen their eligible equal-depth pair over connected x,y; cutting a distinct active-root edge y cannot disconnect u and v. Thus AC does not occur at this first remaining pair.

If u,v are already a common cherry, merge them to d. The pair x,d is nontrivial by the following depth observation, which will also be used for the B child below. Immediately after deleting y, x cannot be sibling to LCA(u,v). If it were, both u and v would be deeper than x. Reinsert the deleted y edge and its suppressed parent to recover J's geometry. An insertion off the exclusive incoming x edge cannot make x deeper relative to u,v: it either changes neither depth, changes both equally, or increases a u/v depth. Insertion on the exclusive incoming x edge makes x,y a common cherry, contrary to J being nontrivial. The same argument applies component by component; disconnected x and u,v cannot be siblings in the first place. At J the source tie rule required x to be at least as deep as both u and v. Thus x,d is nontrivial and Lemma 3 applies without an extra invocation.

For a one-child rule on u,v, pessimistically allow its child to merge x with the remaining local root for free. It spends at least one cut and the terminal barrier spends another. Thus `I(C) <= alpha*2^(k-2)-1` (`four_root_single`). If its child does not merge for free, Lemma 3 is stronger. For BCY's two children, each spends at least two cuts; even allowing both free mergers gives `I(C) <= alpha*2^(k-2)-3` (`four_root_bcy`).

It remains to examine A2BC or A3BC. If its all-pendant B branch is illegal, at most the two endpoint branches survive. Each spends one cut and reaches a nontrivial two-root state: a new common cherry would require RB to have applied before A2BC/A3BC. Lemma 3 bounds each surviving child by `alpha*2^(k-3)-1`, so their sum plus the parent is at most `alpha*2^(k-2)-1` (`four_root_two_endpoints`). No stronger distance claim for the C child is needed in this case.

Now suppose the B branch is legal. We may include any illegal endpoint branch as a nonnegative overestimate, and analyze all three nominal branches. Their A and C endpoint children cannot create an x–survivor common cherry: that would mean x was sibling to u or v and RB would have preempted the parent. The all-pendant B child cannot produce a common x–d cherry either. A surviving x that is not itself cut can become sibling to the merged u,v root only if x was sibling to LCA(u,v) before the cuts: pendant cuts leave the LCA and its incoming edge unchanged, and suppressions below it only contract the two endpoint arms. The depth observation above excludes that configuration. Hence the strong Lemma 3 estimate applies in the A and B children.

In the C child of this u,v branching, both x and u are protected. This is exactly the state where the literal annotation can be P={a,x,u}, Q={x,u}; no cap-two premise appears. If x and u are disconnected, both endpoint cuts are forbidden and this child is dead. If they are connected, the x–u pair is nontrivial and has at least two pendant nodes. To see the latter, let r=LCA(u,v) immediately before cutting v. Orientation makes the u arm at least as long as the v arm. If x is outside r's subtree, the u-arm pendant(s), plus the other arm's residual when necessary, give at least two. If x is in a pendant subtree w, w is not x itself because the parent's B branch was legal and x is protected. If w is not u's sibling, two intervening pendant nodes remain. If w is u's sibling and x is its child, BCY would preempt A2BC/A3BC; otherwise the distance from w to x contributes the second pendant. These are the explicit source p121 alternatives, re-derived here with x,u,v in place of a,u,v.

Both endpoints protected leave only all-pendant cuts. They spend at least two cuts, and the terminal barrier spends one more. This gives `I <= alpha*2^(h-3)-1` for this two-protected local pair at budget h (`both_protected`). Consequently, at C's budget k:

* A2BC on u,v: `1 + [alpha*2^(k-3)-1] + [alpha*2^(k-4)-1] + [alpha*2^(k-4)-1] = alpha*2^(k-2)-2`.
* A3BC on u,v: replace the middle term by `alpha*2^(k-5)-1`, which is smaller.

These are `four_root_a2` and `four_root_a3`. This is a joint local calculation retaining the actual geometry, not a free transition system on |P| and |Q|.

## Budget boundary and use site

For k>=4 the displayed allowances are positive at every cost that is used in the proof. Costs larger than the minimum can be relaxed to the minimum because the full legal call tree is monotone in budget. This uses full call-tree counts, not short-circuit execution. For k=-1,0,1,2,3 the crude full ternary-call bound is respectively 1,4,13,40,121; at alpha=128 the claimed C allowances are 15,31,63,127,255. Thus these small budgets are covered. This finite arithmetic is Lean checked.

If the A/B child allowances at J are separately established as `alpha*2^(K-2)-2` and `alpha*2^(K-3)-3`, the candidate C result composes to `1+I(A)+I(B)+I(C) <= alpha*2^(K-1)-5`, hence the requested bound with -2. The exact affine use-site is `joint_target`. The A/B allowances are explicit external hypotheses here; this route does not certify their complete induction.

## Evidence and limits

The independent-from-other-route Python implementation reproduces the five shared controls and a new arbitrary-double-cut negative control with a positive twin. It samples arbitrary locally admissible states satisfying the outside-b condition; those random states are not claimed reachable from an unprotected top-level input. The nine/thirteen-leaf JSON traces are the retained structural reachability controls, not asymptotic evidence. The alpha choice, leaf/budget inequalities, and conditional affine compositions do not establish the unformalized source geometry.

Formal scope: Geometry.lean proves twelve arithmetic/structural lemmas and one explicit negative fact. It has only standard Lean axioms (reported in the log), no custom axiom, no sorry, and no native_decide. The failed Mathlib import and earlier checker bugs remain preserved. A fresh nonauthor verifier must especially attack Lemma 5's no-free-B-merger step and the proposed frontier credit-reset interface.
