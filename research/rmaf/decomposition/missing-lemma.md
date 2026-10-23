# Open structural lemma from finite synthesis

Let T,T' be ordinary rooted binary trees on X, without rho augmentation.
Let (a,b,c) be a common ordered3-chain in the primary kernel-paper sense:
parent(a)=parent(b) or parent(parent(a))=parent(b), and
parent(parent(b))=parent(c). Let R=T|(X−{c}) and R'=T'|(X−{c}).
Define P(R,R';a,b) as the minimum size of a rooted agreement forest of R,R'
subject to a,b belonging to the SAME component (they need not be singleton
or form the entire component).

**Candidate, OPEN:**

    K(T,T') = P(R,R';a,b).

Every25416 corpus row retained by penalty_synthesis has this equality; the
search included all1260 five-label chain cases, the7-label exact killer,
22155 pairs in the complete fixed-chain7-label family, and2000 seeded8-label
samples. This finite evidence is not a proof and independence/fresh oracle
verification remains required. Penalty(0,1,excluded) also survived; the corpus
does not identify a unique table.

## Exact obligations

1. Lifting: every reduced valid forest with a,b in one component extends by
   inserting c in that component, with unchanged component count and no span
   overlap, in both rooted trees.
2. Normalization: some minimum forest of the original pair can be chosen so
   that a,b,c share a component. A proof must include all forest arrangements,
   especially components joining the lower versus upper exterior of the chain.
3. Mark propagation: repeated replacement by2-chains carries the same-component
   constraint through subtree reduction,3–2-chain reduction, decomposition,
   and every branching step. Existing unmarked-tree safety lemmas cannot be
   silently reused.

A possible normalization proof mechanism is to reroute the at-most-two exterior
components that traverse the common-chain spine. Whether their induced cuts
can always be composed at a cost of at most two extra pieces, including rooted
attachment constraints, is the precise unproved point. No correctness theorem
has been imported as an axiom.

## Consequence and limit

If obligations1–3 hold, a constrained kernel with shorter chains becomes
possible. Under the EXISTING generator-side setup, allowing at most two leaves
on every ordinary edge side gives the arithmetic bound7 d−2, where d is rSPR
distance. IndependentMinima.lean checks only that counting inequality. It does
not establish the new marked-kernel generator correspondence, its safety, or
a faster exponential base. A smaller input kernel alone does not improve the
baseline O*(2.3391^k).

## Replayable next experiment

Generate rooted trees with TWO disjoint marked common3-chains and alternating
attachments outside both spines. Test the joint same-component restrictions
with the independent partition/span oracle, followed by a fresh separately
implemented checker. Test marker propagation on the retained7-label killer and
its rho-augmented version. Refutation should be retained with exact forest
blocks; no-fire keeps this lemma OPEN. Pilot before expanding label count.
