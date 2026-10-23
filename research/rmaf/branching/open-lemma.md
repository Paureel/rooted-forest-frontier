# Three-component residual rebalancing

Status: OPEN. No faster rMAF algorithm is claimed.

Let `opt(T,F)` be the minimum number of further edge cuts required to refine
the current forest F into an agreement forest with rooted tree T, under the
ordinary, unaugmented convention in §2 of arXiv:2409.18634v2. The initial
component parameter K corresponds to K−1 available cuts.

## Exact proposed missing lemma

For every rooted binary tree pair `(T,T′)` with the same labels, after the
paper's tidying operations, for which none of Figure16 steps2a–d apply, there
is a choice of orientation and a cherry `{a,b}` with Whidden parameter t=2
such that the two-pendant-cut child `(T,F)` has the following constructive
property. In polynomial time in the input size, a procedure either solves
that child exactly, or constructs at most three descendant tree-forest
pairs with charged further cuts `d_i ≥ 1`, such that:

1. each descendant is obtained by explicit valid cuts and the paper's
   optimum-preserving tidying operations;
2. `opt(T,F) = min_i (d_i + opt(T_i,F_i))`;
3. the decrease vector is componentwise at least one of `(2,2,2)`,
   `(1,3,3)`, or `(1,2)`; fewer branches are allowed;
4. cut choices, reconstructions, termination, and the polynomial overhead
   are explicit, independent of an optimum oracle.

For budget-limited decision calls, equality is understood with the usual
failure value when every branch exceeds the remaining budget. The rule must
work for every remaining cut budget, not just the optimum on small inputs.

The permitted delivery can be broadened to larger generated splitting cores
provided their exact weighted branching sums are no larger than the above
vectors and their generation time is polynomial per emitted child. That is
a versioned change to this pinned lemma, not an implicit assumption.

## Why this particular lemma matters

It would replace the worst two-cut child's current vector `(1,2,2)` from
Lemma16. Including the two original one-cut cherry branches yields overall
vectors `(1,1,4,4,4)`, `(1,1,3,5,5)`, or `(1,1,3,4)`.

At c=231/100 the first two sums are respectively
`921759400/949132107` and `642840264200/657748550151`, both below 1.
The third is smaller than the published vector `(1,1,3,4,4)` by one
`c^-4` term and is also below 1. Every other printed worst rule passes this
c, the tightest being Lemma13: `1/c + 3/c^2 = 5900/5929 < 1`.

Thus this lemma, together with full correctness and overhead proofs for the
published rules and the new macro rule, would imply O*(2.31^K). Arithmetic
certificates have been kernel-checked in Lean; the structural hypothesis and
the full recurrence solution have not been formalized. This is a conditional
research direction, not a proved improved algorithm.

## A more structural sublemma to attack next

Let a three-component forest have labels A,B,C. Assume A and C are
homeomorphic, B is not; `T[A]` overlaps `T[B]`, `T[B]` overlaps `T[C]`, and
`T[A]` is disjoint from `T[C]`. Does there exist an overlap edge
`e ∈ T[A]∩T[B]`, an overlap edge `f ∈ T[B]∩T[C]`, and an optimal refining
agreement forest such that either:

- every resulting B-component avoids both e and f in T; or
- every resulting A-component avoids e, and every resulting C-component
  avoids f?

This is an exchange assertion: it excludes the two mixed edge-allocation
families. It survived 2,640 exact synthetic states with block sizes 2,3,2.
These states are not asserted reachable baseline children. It is OPEN.

Even a proof of this sublemma alone would not prove the full macro lemma:
the three-color splitting-core bound and the remaining asymmetric overlap
cases must also be controlled.

## Replayable next experiment

Generalize `synthetic_exchange.py` to block sizes 2,4,2 and 3,3,2. Freeze those
families and the exchange predicate before running; pilot structural scans
and oracle calls separately. Search for a mixed-allocation optimal forest
that cannot be exchanged. If found, pin its topology and identify a further
restriction that is actually forced by Whidden reachability. If it survives,
construct an explicit exchange proof and send it to a fresh adversary before
formalizing it.

Then synthesize candidate cut macros over actual reachable hard children;
score them by exact coverage and rational branching mass, rather than merely
counting cuts or deleted leaves.
