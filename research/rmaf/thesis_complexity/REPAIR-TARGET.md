# Runtime repair after independent review

The completed review is `../thesis_complexity_review/report.md`. Preserve all
original proof sources, traces and receipts. Work in a new `repair/` directory.

Target: repair the joint descendant bound in the literal Chapter 6 G4.1 case
with P={a}, Q empty and three pendant nodes, and account for reachable
three-credit states. The desired inequality is

`1 + I(A) + I(B) + I(C) <= alpha * 2^(K-1) - 2`.

The source's separate child allowances give coefficient 9/16 instead of 1/2.
A sufficient C-child estimate is `I(C) <= alpha * 2^(K-3) - 1`, but that is
a target, never a granted premise. `../thesis_complexity_review/local-repair.md`
proposes a geometric repair only when the local uncle has two active leaves;
it is newly authored and requires an independent adversary and proof review.
Three/four active leaves and the three-credit state remain open.

MAY ASSUME: the exact source rules, explicit valid-state hypotheses, and
smaller-budget induction hypotheses stated verbatim. State the unary-rho
convention. MAY NOT ASSUME: a two-credit cap, universal validity of the
proposed repair, a missing structural descendant bound, or universal
short-circuit reachability of the supplied traces. Do not read or depend on
the separate correctness/transfer work to certify runtime.

Freeze controls before constructing the repair: reproduce the nine-leaf
9/16 substitution and immediately dead C-child; the thirteen-leaf |P|=3
assignment; the live two-active-leaf example; and the wrong-orientation
mutation with its passing twin. Keep credit sets distinct from protected
edge sets. Existing finite traces are controls, never an asymptotic proof.

Apply prove-protocol: adversary first, then distinct geometric local-history
and recurrence/state-invariant routes without cross-reading. An enlarged
credit domain alone is insufficient. Licensed outcomes are a universal
joint bound, an explicitly conditional narrower theorem, or a precise
reachable counterexample naming the next missing invariant. Preserve every
failed formulation. Lean-check all proved arithmetic and structural claims;
mark ordinary mathematical arguments separately until formalized. A new
proof needs fresh nonauthor verification and exact use-site composition.

Own `repair/`, `../results/thesis-runtime-repair-*`, and
`../progress/thesis-runtime-repair.json`. Keep artifacts local, records atomic,
metrics an object and lemmas/claims objects with id,label,status,detail.
Do not alter the aggregate theorem count. Use Astra xhigh for fresh agents,
at most two simultaneously active child agents; stage further review after
those finish. No steering of running proof agents.
