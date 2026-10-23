# GLOBAL-Q: remaining safe-cover construction

The required cover and faster algorithm remain open. This route proves the original-edge refinement direction in Lean, gives a residual-budget argument in prose, rejects two precise quotient proposals by exact witnesses, and implements a total exhaustive fallback whose cost exceeds the licensed bound. The finite tests use a development oracle written by this route. They still require fresh independent review.

## Original edges

Let S be the original source tree, K an original nonredundant optimum cut set, and C a subset of K. An edge-deletion component contains its full original vertices, including vertices suppressed in the displayed rooted restriction. A K-path avoids every C edge. Therefore each K-component is contained in one C-component. The leaf partition of the original optimum refines the precut leaf partition.

`EdgeLocalization.lean`, theorem `original_optimum_refines_precut`, proves this statement for arbitrary graph adjacency and original-edge cut predicates. The theorem uses no axioms. `residual_reach_exact` proves that deleting C and its residual K\\C is exactly deleting K. Its axiom audit contains only propext, Classical.choice and Quot.sound. Neither theorem supplies a pure-bridge or triple graph implementation.

Inside a C-component D, let q_D count residual K edges with both endpoints in D. The induced source graph of D is a tree. Deleting those q_D edges creates q_D+1 original optimum regions, all nonempty. Their original optimum pieces form a local agreement forest of D and the corresponding target restriction. Thus the original unmarked local distance satisfies d_D≤q_D≤|K|-|C|. This uses the original cut and local partition definitions in the preserved note, lines17-26. It does not use marked-query budgets.

If |K|=b and |C|≥b-floor(b/2), then every d_D≤floor(b/2). The Lean theorem `half_residual_bounds_each` checks the arithmetic once the graph/local witness inequalities hold. If |K|≤b, choosing ceil(|K|/2) cuts gives the stronger d_D≤floor(|K|/2)≤floor(b/2). Finding K is an obligation of the proposed algorithm; K appears only in this existence argument.

## Failed one-edge proposal

Q2-ONE asserted that each optimum quotient admits one edge whose deletion leaves at most floor(b/2) internal optimum edges in every component, for b≥1.

For S=(((((a,b),c),d),e),f) and T=((a,c),((b,e),(d,f))), exact original-source-edge enumeration gives optimum 3. The cut set isolating b,d,f is an original optimum, with remaining component {a,c,e}. Contracting the full source components gives a three-spoke star. Each of the three possible one-edge precuts leaves quotient residual counts 2 and 0. Recomputing within the same development instrument gives original unmarked local distances 2 and 0. The required threshold is floor(3/2)=1.

The receipt is `algorithm-balanced-cover-quotient-probe.json`: 176 original cut sets examined through the first successful cut count, 19 optimum realizations. The source-cut oracle passed four literal optimum controls and caught three predeclared corruptions before this search. The local calculations share that oracle and are development checks.

A connected quotient with one or two edges has a one-edge split whose remaining internal edge counts are at most floor(b/2). Hence b=3 is the smallest possible quotient budget for this failure. The same development instrument checked all rooted labelled pairs with at most five leaves, including 105² five-leaf pairs; all had optimum ≤ 2. This finite census supports six leaves as the smallest ordinary source pair for Q2-ONE. It does not independently certify the oracle or imply a universal result beyond these inputs. The five-leaf census took 2.985534040999937 s after a four-leaf pilot and recorded projection.

All three two-edge subsets of this recorded optimum repair the example. Each has precut cost 2, a pure-bridge forest with tau=1, and completion cost 1, giving charged total 3. Receipt: `algorithm-balanced-cover-quotient-star-repair.json`.

## Failed arbitrary-half proposal

Q-HALF-ANY asserted that every ceil(b/2)-subset of an original optimum cut set produces a terminal forest in addition to the residual-budget guarantee.

For S=(((c,(a,b)),d),((e,f),g)) and T=((a,(((e,(c,d)),f),g)), exact enumeration gives optimum 2. Cutting the source subtree {a,b} and the source subtree {e,f,g} gives an original optimum with regions {a,b}, {c,d}, {e,f,g}.

Precut only {e,f,g}. The remaining four-leaf component {a,b,c,d} has local distance 1, so tau=1 meets the half-budget bound. Its target hull overlaps the {e,f,g} hull at a vertex having degrees 2 and 3 in those hulls. The overlap is impure, and the four-leaf component is incompatible. The forest therefore fails both terminal recognizers. Precutting only {a,b} instead gives a pure balanced forest. This example rejects the word "every" in Q-HALF-ANY; the existential safe-cover condition survives it.

Receipt: `algorithm-balanced-cover-quotient-geometry.json`, with 79 original cut sets examined and 2 optimum realizations. A pure crossing positive control and an impure degree-three corruption preceded the new geometry test. These inputs are ordinary rooted binary pairs. No unspecified reduction history is inferred from them, and neither witness refutes the reduced-instance safe-cover target.

## Total fallback

`SlowCover.py` gives an explicit total generator, decision procedure and optimization wrapper. It validates the ordinary binary input and distinct original labels, then enumerates every subset of at most min(b,n-1) original source edges. It rejects empty source components and checks the rooted restrictions and unsuppressed target supports. It emits only complete agreement-forest certificates.

Each certificate records its original source edges, every component's full original source vertices, original labels, rooted restriction, target support, precut cost r and residual cost 0. Its component count is r+1 and charged total is r. Every emitted forest is all-compatible, so it is a compatible/triple terminal instance and its local distance is zero. Completion uses the displayed witness directly and makes zero local optimizer calls. No root label is added.

To prove original-optimum survival, start from any agreement partition P with m nonempty, vertex-disjoint source supports. Assign each support its own region. Repeatedly assign an unassigned source vertex adjacent to an assigned region to that region, using any fixed deterministic order. A frontier exists until all vertices are assigned because the source tree is connected. Each region remains connected and retains its original nonempty label block; all leaf labels were assigned initially. Cut exactly the edges joining distinct regions. Contracting the regions gives a tree on m vertices, hence exactly m-1 original boundary cuts. No resulting source component is empty. The generator examines that cut realization of P, so the original optimum itself is emitted when its cut count is at most b.

Every output is a valid agreement forest. A budget failure is correct because the preceding realization argument covers every agreement partition of cost≤b. Iterating budgets 0,...,n-1 terminates: the singleton partition has an original-source cut realization with n-1 cuts. The first successful budget is optimal, with direct original-label reconstruction and no reduction history to invert.

For a source with n leaves there are N=2n-2 original edges. The charged candidate count is

    sum_{i=0}^{min(b,n-1)} binomial(N,i).

The algorithm processes every candidate in polynomial time, including failed recognitions and output serialization. It therefore takes polynomial(n) times this sum. This bound fails the licensed alpha^b requirement. Four fixed cases passed and four incorrect-accounting twins were rejected; the crossing case produced all six distinct optimum leaf partitions. Receipt: `algorithm-balanced-cover-quotient-slow-controls.json`. These checks verify finite cases of the implemented fallback, not its universal prose argument.

## Guarded quotient route

After two rejected formulations, this route changes to GLOBAL-Q-GUARDED. A candidate certificate consists of original precuts C, full source components, a polynomially checked pure-bridge or compatible/triple certificate, and local agreement witnesses requiring at most floor(b/2) additional cuts per original component. Every cut count refers to original edges, and every local witness is checked by rooted topology and unsuppressed disjoint supports. Verification is polynomial in the explicit certificate size; it does not compute tau by an uncharged solver.

The remaining lemma is an oracle-free enumeration theorem. On every reduced input (S,T,b), enumerate a family of these guarded certificates within O*((3/2)^b) total size and time, such that if the original optimum is≤b then at least one original optimum cut realization K has an emitted C subset K. The original-budget and terminal requirements apply to every emitted forest, including outputs on unsuccessful decision inputs. The prelicensed fraction is1/2. A proof must include rejected certificates and all local-witness construction work in the same bound. This statement is still open. Full-cut enumeration proves existence and totality at the larger binomial cost; it supplies no smaller-base certificate.

## Arithmetic and acceptance

`EdgeLocalization.lean` proves exact rational comparisons

    2 < (142/100)^2,
    (9/4)*(1+142/100) < (23391/10000)^2.

Since sqrt(2)<142/100, these imply the conditional numerical inequality (3/2)*sqrt(1+sqrt(2))<23391/10000 using monotonicity in an ordered real field. The Lean file proves the displayed rational comparisons, plus a nonvacuous inequality for rational s with 0≤s and s²≤2. A real radical implementation is not formalized here. The arithmetic alone does not establish generation or any complete algorithm base.

`NegativeArithmetic.lean` kernel-checks the false-exponent negation and the repaired/failed star twins. `FalseStar.lean` fails with an explicit false-proposition diagnostic. `FalseExponent.lean` fails reduction when asked to prove the false comparison; its negation is independently kernel-checked in NegativeArithmetic. The final accepted Lean logs contain no sorryAx, custom axioms or native_decide. The unsuccessful arithmetic draft is retained as a text file and pilot log.

Algorithm, Correctness and Smaller base remain open for the requested faster algorithm. Pure-bridge G1-G7, triple G1-G3 and reduction/executable correspondence remain conditional imports. A fresh nonauthor source-model review, witness reconstruction, code replay and interface trace are still required before this route receives independent verification. No novelty or unrestricted speed record is claimed.
