# Actual minimum-rank dichotomy

Author Lean proofs establish the pinned output, cost, and raw-list mass
statements for the unchanged source generator. Fresh nonauthor verification is
pending. The complete rooted-MAF algorithm and all three main milestones remain
OPEN. No novelty claim is made.

Let r be the number of distinct colors on the original input labels. A rank-r
source partition passes the original partition and disjoint-minimal-embedding
checks, has monochromatic blocks, and has r blocks. For a proper original tree:

* If such a partition exists, every q<r−1 returns the empty output list. Every
  q≥r−1 returns exactly one literal output, with r−1 actual recorded original
  cuts. Each block contains exactly the original labels of one realized color.
* If no such partition exists, every actual emitted output has at least r
  recorded original cuts.
* If every actual output has cost at least L≥r−1, then for rational c≥2,
  the literal sum over the output LIST satisfies
  `sum c^(-cost) ≤ 2^(L-(r-1)) c^(-L)`. With rank-r infeasibility, L=r gives
  `sum c^(-cost) ≤ 2 c^(-r)`.

The proof uses the completed original source-coverage theorem to obtain a
cost-r−1 member at budget r−1. Budget monotonicity keeps that member at larger
budgets. Its dyadic weight is the entire actual raw-list mass allowance.
Strict positivity excludes a second entry, including a duplicate. Counting
block representative colors proves the stated exact class memberships. The
coordinator accepted this equivalent proof route; the original target's
suggested operational forced-step construction remains unchanged as history.

For the infeasible case, an actual output of cost r−1 would have r blocks by
the original cut/component realization. Its proved partition, embeddings, and
monochromaticity would be a rank-r source partition. This contradicts the
infeasibility premise. The mass proof compares each actual term with its
dyadic term and applies the actual generator's proved dyadic bound. The
dyadic domain is discharged by a theorem about the executable generator.

Rank-r feasibility can be tested directly on the original color classes.
Form the r nonempty lists of labels of each realized color, then run the
existing original-label partition and embedding checks. If those checks pass,
the lists themselves provide a rank-r source partition. Conversely,
`rank_partition_color_classes` proves that any feasible rank-r partition has
exactly these memberships; minimal embeddings depend only on membership.
The test therefore decides source feasibility without computing an optimum.
Filtering labels and running the finite tree/list embedding checks takes
polynomial work in the explicit input size, including for bounded r. The
membership theorem is Lean-checked; this arm adds no Lean complexity model
or separate boolean equivalence theorem for the canonical test.

The preproof receipt retains ten positive statements and three rejected false
propositions. The isolated replay rebuilt 51 modules and audited all 2,194
module-origin declarations, including generated/private declarations. The
observed axioms were `Classical.choice`, `Quot.sound`, and `propext`.
Missing-record, foreign/private custom-axiom, and changed-source controls all
failed as intended. These are author checks. The completed all-colored census
is declared development contact and was not rerun; its large raw receipt was
not read.

The replay certificate is
`results/algorithm-universal233-rank-replay-20261015T091933Z/certificate.json`.
`INTERFACE.md` gives exact hypotheses and theorem names; `FIRST-GAP.md` states
the remaining independent acceptance condition.
