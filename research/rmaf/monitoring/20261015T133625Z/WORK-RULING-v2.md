# Work and cost ruling

The rebuilt theorem supports the printed bound on the declared rational bill. Its formal premises are exactly ordinary, ordinaryWork, fixed optional target T, budget cap Q, rational c and K, c>=2, K>=0, LocalBillBound, a literal source list ss, q<=Q and proper T ss. The signature has 13 explicit binders and no supplied OrdinaryIH argument; `SIGNATURES-AND-CLOSURES-v1.json` retains the exact type. `PREMISE-TRACE-v2.md` reproduces the definitions and consuming source lines verbatim.

The immediate hypothesis is:

```lean
def LocalBillBound (ordinary : Tree → Tree → Nat → Option Forest)
    (ordinaryWork : Tree → Tree → Nat → Nat) (T : Option Tree) (Q : Nat) (c K : Rat) : Prop :=
  ∀ ss q, q ≤ Q → proper T ss = true →
    (nonrecursiveBill ordinary ordinaryWork T ss q : Rat) ≤ K*c^q
```

The quantifier includes every proper current source list for the fixed original target, and every budget up to Q. It therefore covers every actual recursive child. `branch_paid_proper` establishes proper replacement and 1<=d<=q for every raw occurrence; the source-core rational mass is summed over both full lists with duplicates. Strong induction bounds each child's factor q-d+1 by q, then the mass bound <=2/c<=1 gives at most q*K*c^q for all forest children. Adding the immediate K*c^q gives `(q+1)*K*c^q`. This argument neither assumes a total forest-runtime bound inside LocalBillBound nor inserts the desired polynomial coefficient as a proved fact.

The printed bill contains separate terms for source-core prefixes, refusals and pruned attempts, original-target coloring on the selected source's original leaves, ordered-pair target-span search, every emitted source replacement/materialization, minimum/final checks, and metered ordinary dispatches at the actual problems and budgets. At crossed q0, the actual generator receipts have no outputs but visited=1, childAttempts=1 and pruned=1 for each parent. The ordinary schedule also records lower-bound refusal with no callback and retained caller work. Zero-output cases therefore remain part of the source bill.

The conservative inspection sheet `4096*(targetNodes+sourceNodes+sourceCount+q+1)^8` is declared in ForestWork.lean. The fresh compile proves theorems about the defined meters and recurrence; it does not identify every primitive operation of the production functions with that sheet. A primitive proof must also account for the sizes of returned ordinary payloads before original-state checking. The correctness IH bounds valid ordinary answers through label coverage and minimum; the work theorem itself accepts an arbitrary callback. Any transfer from the abstract bill to actual source work must state the callback-output/ordinary-work convention used for those checks.

`proper_source_size` proves `sourceNodes ss+ss.length=2*|labels T|`, and each emitted child is proper. This bounds source-tree volume without adding labels. It does not establish a polynomial K from an ordinary-work IH, charge unbounded Nat bit operations, or prove compiled-machine semantics. FIRST-GAP.md explicitly leaves these obligations open. The source-operation convention also excludes the cost of evaluating the accounting functions themselves.

The actual released generator realizes the originally specified false below-c2 vector. For `T=((0,(2,4)),(1,(3,5)))`, `ss=[(0,1),((2,3),(4,5))]` and q2, the selected original vertex is [] and the concatenation of both full raw lists has costs `[1,2,2]`. Exact mass is 1 at c2. At c=3/2 the mass is 14/9, exceeding 2/c=4/3. This post-contact realization rejects an extension below c2 and confirms that the two distinct d2 occurrences cannot be collapsed by cost. It does not challenge the stated c>=2 theorem.

Ruling: the rational bill recurrence is CONFIRMED under its printed LocalBillBound, c/K, properness and cap premises. The transfer to a conservative primitive source-operation envelope and a polynomial coefficient is QUALIFIED/OPEN. Full ordinary/mutual runtime, scalar bit costs, compiled instructions and any improved global base remain OPEN. Finite execution timings are used only to plan these bounded checks.

In that q2 mass realization, the d1 branch's residual disjoint call has budget1 and returns none; both d2 occurrences remain affordable. The failed d1 occurrence still contributes its mass. This checks the failed-child accounting separately from the q0 zero-output/pruned-prefix accounting.
