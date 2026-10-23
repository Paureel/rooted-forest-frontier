# Conditional exact consumer and paid stopping facts

Status: constituent proofs submitted for kernel checking; safe-cover generation and whole algorithm remain OPEN. The existing toolkit and problem-specific guide were consulted before this one-shot proof/interface code. No existing tool generates a safe cover; `ConsumerCore.lean` supplies only generic consumer logic and natural-number arithmetic.

Let Generate return a finite list of original source-cut certificates F. For each F, Complete must return an exactly minimum valid original-label agreement partition refining F, with its total original cut cost. If every returned partition is globally valid and at least one original optimum refines one F, then the least computed cost equals the original optimum. This needs one optimum, and requires no all-optima representative family. `one_optimum_suffices` proves this conditional statement. `conditional_decision_exact` needs coverage only when the original optimum≤b; valid returned forests can never cause false acceptance.

The source-cut interface is load-bearing: if r nonredundant precuts induce m=r+1 components and completion returns p≥m final pieces, total=r+(p−m)=p−1. If s finished components were removed, use m_live+s=r+1 and reinsert those s components; total=r+(p_live−m_live)=p_live+s−1. Both identities are separate Lean propositions. Empty or redundant source cuts violate m=r+1 and cannot enter these propositions.

For a global feasible completion of residual budget b−r, the local optima are dominated by the actual extra cuts in the respective components, hence sum d_D≤b−r. Thus at most one component can have d_D>b/2. This useful arithmetic fact does not locate that component cheaply, and does not certify purity. If r≥b/2, every d_D≤b−r≤b/2; however waiting for that depth at a classical branching frontier costs c^(b/2) before paying another c^(b/2) for completion and yields base c again. No improvement follows from stopping depth alone.

Conditional algorithm schema (OPEN interfaces are named in IMPORTS.md):

```
DECIDE(S,T,b):
  validate distinct equal labels and binary rooting
  reduce using safe original-label reconstruction records
  cover = GENERATE-PAID-COVER(S,T,b)               # OPEN
  best = failure
  for cut_certificate in cover:
    realize original nonredundant cuts; verify r≤b
    classify target overlaps / compatible-or-triple topology
    if compatible-or-triple:
      answer = EXACT-TRIPLE-COMPLETION             # G1–G3 OPEN
    else if pure-bridge:
      obtain original unmarked tau≤theta*b certificate # OPEN, paid
      answer = EXACT-PAID-PURE-COMPLETION           # G1–G7 OPEN
    else: reject invalid generator output
    reinsert all completed components and undo reductions
    verify actual agreement partition; total = r + residual
    retain least total if total≤b
  return best
SOLVE(S,T):
  for b in 0,...,n−1:
    answer=DECIDE(S,T,b)
    if answer succeeds: return answer
```

No optimum oracle is used in the schema. Existence of singleton partition gives finite termination once the interfaces are actually implemented and proved. Paid role-swap queries for pure completion must use q_J=h_D(J)−(r_J−1)≤d_D and second budget mu−(r'_J−1)≤d_D, rejecting negative budgets immediately; counting h_D(J) itself as local FPT budget would be wrong. At most2m local calls and all failed deepening budgets are charged to O*(c^tau), conditional on their exact solver/interface proofs.

If generation/detection/reconstruction costs O*(alpha^b), number of outputs O*(alpha^b), and every completion costs O*(c^(theta*b)), then all costs are O*((alpha*c^theta)^b). This includes generation and all queries. Geometric iteration of budgets changes polynomial factors only for composed base>1. These are conditional implications. No actual alpha^b generator is yet supplied.

The frozen weaker numerical target alpha=3/2, theta=1/2 has a rational upper certificate: sqrt2<283/200, local c<483/200; alpha² c<4347/800<49/9, so composed base<7/3<23391/10000. Lean retains each integer cross-product certificate. Those arithmetic facts prove no runtime without a paid cover construction.
