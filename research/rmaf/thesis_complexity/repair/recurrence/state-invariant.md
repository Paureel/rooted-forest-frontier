# Conditional continuation invariant

The runtime repair remains conditional. We prove arithmetic for a finite set of credit states and for a finite continuation certificate. We do not prove that every source-reachable G4 continuation has such a certificate. The two-active-leaf lemma is neither imported nor assumed.

## States

A normalized local state records `(phase, r, p, q, mode)`:

- `phase` is G4.1, G4.2, G4.3, G5, boundary, or terminal.
- `r` counts remaining active roots-todo units in the local F1 subtree together with the inherited endpoint. The proposed local interpretation uses `0≤r≤5`; its source-wide rank property is a structural obligation.
- `0≤q≤p≤3` are cardinalities of analysis sets with `Q⊆P`. Protected edge sets are additional algorithm data and are never reconstructed from `(p,q)`.
- `mode` is ordinary, hard-C, or soft-C. The last two modes are continuations of the exceptional G4.1 A3BC C branch with incoming Q empty or nonempty, respectively.

This gives a finite annotation set. It does not make every formal transition between annotations an algorithm transition. An actual forest pair, its protected edges, its chosen oriented sibling pair, and its exact cut set must witness every step. In particular, no deletion-closure assumption appears here.

An ordinary state's proposed allowance is

`U(k,p,q) = alpha*2^k*w(p,q) + p - 3`,

where `w(p,q)=(1/2)^(p-q)*(3/4)^q`. An endpoint in `P\Q` is a hard credit, and an endpoint in Q is a soft credit. These names mean only the multipliers in this proposed allowance. They do not describe a theorem about protected edges.

| p | q | w | offset |
|---:|---:|---:|---:|
| 0 | 0 | 1 | -3 |
| 1 | 0 | 1/2 | -2 |
| 1 | 1 | 3/4 | -2 |
| 2 | 0 | 1/4 | -1 |
| 2 | 1 | 3/8 | -1 |
| 2 | 2 | 9/16 | -1 |
| 3 | 0 | 1/8 | 0 |
| 3 | 1 | 3/16 | 0 |
| 3 | 2 | 9/32 | 0 |
| 3 | 3 | 27/64 | 0 |

The multiplicative choice is derived from exact local composition: a soft credit that discharges into generic children at costs one and two has multiplier `1/2+1/4=3/4`. Repeating that construction multiplies the factors. The original additive formula gives `1/2` for `(2,2)`, whereas a formally lifted two-child discharge contributes `9/16`. The latter is an arithmetic obstruction to unrestricted template lifting; this route does not assert that this particular two-child transition is source-reachable.

## Transition contracts

For a branch with current state `(p,q)` and children `(d_i,p_i,q_i)`, ordinary composition requires

`sum_i 2^(-d_i)*w(p_i,q_i) ≤ w(p,q)`

and

`1 + sum_i(p_i-3) ≤ p-3`.

The leading 1 counts the current invocation. `RepairArithmetic.lean` checks the finite branching and discharge families actually enumerated in `liftedRows` and `dischargeRows`, plus the G4.1 cases with at least four pendants. Python checks the same 37 explicitly listed schemas. Exactly 35 pass the multiplicative allowance. The two failures are G4.1's three-pendant reset, for incoming `(1,0)` and `(1,1)`.

The three-credit example has `(p,q)=(3,2)`. Its only legal branch in the frozen trace cuts two pendant edges. The source's lifted assignment returns to the inherited `(1,0)` state. Its leading contribution is `2^-2*(1/2)=1/8`, below `9/32`, and its intercept is `1-2=-1`, below 0. This checks this particular discharge, without imposing a two-credit cap.

Every uncovered source transition requires its own contract. For example, hypothetically allowing a binary cost-one transition retaining `(3,2)` preserves the leading coefficient but gives intercept 1 instead of 0. A hypothetical Case2B reset from `(3,0)` or `(3,1)` has leading coefficient 1/4, exceeding those states' allowances. The exact state-coverage adversary catches all three. Their source reachability is unknown; none is used as an algorithm counterexample.

## Exceptional C states

Let K be the G4.1 parent's remaining budget and let `X=alpha*2^K`. For incoming `(1,0)` and exactly three pendants, the two available child allowances are

`I(A) ≤ X/4-2`, and `I(B) ≤ X/8-3`.

The parent target is `1+I(A)+I(B)+I(C) ≤ X/2-2`. Exact addition shows that

`I(C) ≤ X/8+2`

is sufficient. If A and B attain their individual allowances, this C condition is also necessary. The previously proposed sufficient estimate `I(C)≤X/8-1` is stronger by three invocations. The weaker interface is proved in Lean as `weak_C_exact_interface` and composed in `joint_hard_from_weak_C`.

The hard-C annotation therefore requests allowance `alpha*2^t/4+2`, where its own budget is `t=K-1`. A soft-C annotation requests `alpha*2^t/2+2`. Lean's `joint_soft_from_weak_C` checks the corresponding incoming `(1,1)` composition. Assignment of either annotation is an obligation to provide a certificate below, never a grant of its allowance.

## Frontier certificate

Expand a finite prefix of the **actual legal recursive-call tree** rooted at C. Include every legal child, using a complete recursive-call tree as an upper bound even if an implementation short circuits after success. The prefix stops at terminal invocations or at empty-credit invocations where the smaller-budget induction hypothesis is applicable. Trivial common merges and F2-root removals belong to the current invocation and create no new node.

Let V be the number of expanded invocations, including terminal failures or successes. Let the L unexpanded frontier roots have budget decreases `d_1,...,d_L` measured from C. Their calls are excluded from V. For every frontier root, establish its actual budget and the empty-credit allowance separately. Then

`I(C) = V + sum_j I(frontier_j)`

and

`I(C) ≤ alpha*2^t * M + B`,

where `M=sum_j 2^(-d_j)` and `B=V-3L`.

The simple hard-C certificate is `M≤1/4` and `B≤2`. It is sufficient for every nonnegative alpha. For the declared uniform choice `alpha=128` and parent K≥0, the exact affine condition can be weakened to

`M≤1/4` and `B≤2+64*(1/4-M)`.

For a fixed prefix, this last condition is sufficient for its affine majorant to satisfy the hard-C allowance for every K≥0. If the prefix changes with K, apply the criterion separately to each resulting prefix. The Lean theorem uses the still more direct, exact test on the sum of frontier allowances and therefore does not require either envelope simplification.

The simple certificate covers a dead C, one cost-two empty-credit discharge, one cost-one discharge to a separately certified hard-credit state, or two cost-three empty-credit discharges. The latter two examples use their explicitly stated child certificates. One cost-one empty-credit discharge fails: at X=128, the child may have 29 calls, C has 30, and the requested C allowance is 18. Lean proves the passing composition and rejects a deliberately false proof of this mutation.

## Induction boundaries

The source p117 induction says: "For the inductive step, assume k ě 0 and the bound on Ipk1, P q holds for all k1 ă k and P “ H ." The source uses later groups to justify nonempty-credit intermediate bounds. This route preserves that distinction. A nonempty-credit A allowance is an explicit continuation certificate obligation; it is not silently included in the outer induction hypothesis.

The failure test k<0 precedes the success test, and either terminal invocation counts as one. For `alpha=128`, all ten proposed credit allowances are at least one at k=-4 and hence throughout -4≤k<0. This boundary calculation is kernel-checked. The wider range than the source's -3≤k<0 supports the separate four-pendant arithmetic check. A real cut of more than four edges may produce a budget below -4; that child is evaluated as a terminal call and must not be assigned the formula at its unboundedly negative budget. For a capped arithmetic row one may instead charge an effective decrease four, using the already proved terminal bound at that clipped budget. This is an arithmetic upper-bound convention, not a modified algorithm.

No induction assertion is made for arbitrary `(p,q)` configurations. To apply the finite-state table to a full G4 block, the actual source transitions must obey the table's contracts or have explicit frontier certificates. An optional bounded local construction would use the rank r and prove that every paid local branch decreases r before the next local branch, after all in-invocation normalizations. We have not proved that rank property for all source histories.

## Exact use site

`joint_hard_from_frontier` takes six substantive premises: the A allowance; the B allowance; the exact expanded-prefix invocation identity; a pointwise frontier allowance for each exit; the exact aggregate C-frontier inequality; and the numerical identification `X=alpha*2^K` supplied when interpreting its integer-scaled statement. Its conclusion is the pinned G4.1 target, with every additive invocation counted.

The unproved source premise is existence of such a finite legal-prefix certificate for every relevant C continuation, together with valid A and boundary certificates. In the two-active-leaf case a paid discharge or an immediate dead end would provide it; the claimed geometric exclusion of a free merge remains unproved here. For three/four active leaves, the entire prefix must be checked, including the reachable three-credit state. Proving a credit bound only at individual children is insufficient when a later reset loses inherited credit.
