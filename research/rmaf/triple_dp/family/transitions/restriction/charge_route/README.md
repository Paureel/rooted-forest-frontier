# Conditional parent-index charge proof

This arm proves finite count and cost identities under explicit selection and
root-owner hypotheses. It does not construct the child restrictions, recover
supports by an index bijection, transport the normalized premise, or establish
full G2. The producer's status is **CLOSED-UNVERIFIED for the conditional
count/cost statements**; fresh nonauthor semantic and interface review is pending.

`ChargeCore.lean` sums 0/1 contributions over the original parent index list.
For each parent index, left and right liveness contribute one charge, with
one extra charge exactly when both predicates hold. List induction sums that
identity. A separate nodup argument counts an overlap confined to one
optional parent index. The resulting `count_balance` theorem states

```
weight left + weight right = parent enumeration length + duplicate
```

where `duplicate` is 1 exactly when the optional parent index is live on both
sides. `closedCharge` sums live indices other than the exact optional
child-root owner. The theorem `close_balance` relates this sum to the live
count. `four_charges` then gives all four costs: child costs plus both root
charges, plus the right root charge, plus the left root charge, or plus zero.
The one-sided and two-sided cases explicitly require that the continued
parent index is the appropriate child-root owner. A child-root owner may be
closed in the parent.

`ChargeConsumer.lean` connects these sums to `CostRoute.Family.cost`.
`selected_family_cost` takes equality between the mapped child enumeration
and the selected parent list; it derives the cost equality from that list
and the existing family cost definition. It assumes neither a count equation
nor a transition cost equation. `conditional_family_costs` additionally takes
exact support equivalences, coverage by the two liveness predicates, overlap
confined to the parent boundary, and liveness of each occupied child root.
It proves the four cost equations with the child-root support hypotheses
printed in the theorem. `conditional_family_count` proves the count equation
from the selected-list equalities, coverage, and confined overlap.

Use this arm when those conditional inputs have been established. The Boolean
predicates are explicit parameters. Applying the consumer to a model using
propositional `LiveIndex` subtypes requires the corresponding predicate
identification and subtype transport. Those are not supplied here.

Run a fresh replay from the workspace root with a new label:

```sh
./bootloops-python research/rmaf/triple_dp/family/transitions/restriction/charge_route/replay.py review-01
```

The script refuses to reuse a label or overwrite a receipt. It copies the
three allowed prior dependencies and this arm's sources into a fresh local
folder, compiles with Lean 4.35.0, records theorem and axiom queries, and runs
exact positive and negative controls. Standard axioms reported are
`propext`, `Classical.choice`, and `Quot.sound`; no custom unproved axioms,
`sorryAx`, or `native_decide` are used by the accepted declarations.

The executed `final-v1` replay checked all eight target fixtures, detected
eight wrong-output cases while accepting their clean twins, rejected four
malformed inputs, and excluded the raw nonlive-child-root incursion from
this arm's root-liveness premises. A source-copy comparator mutation let all
eight wrong outputs escape; the outer check rejected it. Four Lean false
goals failed on their propositions, with a malformed import checked
separately. `ConsumerSentinel.lean` supplies actual families and every
conditional premise for T1, using repeated leaf value 7; the theorem yields
parent cost 2 and child costs 0 and 0.

The receipt is
`research/rmaf/results/triple-family-transitions-restriction-charge-replay-final-v1.json`.
Its source pins and per-command logs are retained under `replays/final-v1/`.
Earlier failed proof attempts and the initial control implementation remain
under `attempts/` and `logs/`. The workspace-wide `bootloops-check` suite was
not run by this arm; this evidence concerns these Lean declarations and exact
fixtures only. No external numerical engine was needed.

The numerical checker and proofs share the target fixtures and this author's
reasoning. Their agreement is development evidence. The proof imports only
`FamilyAssembly` and its older dependencies; it does not import the other
new restriction proofs. This arm claims no novelty or algorithmic bound.
