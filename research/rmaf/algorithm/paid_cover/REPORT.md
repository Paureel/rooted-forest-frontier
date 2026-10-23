# Paid safe-cover route v1

Pinned target read: `algorithm/TARGET.md` and `algorithm/PIN.md`, 2026-10-14.

Status: complete algorithm OPEN; universal exactness OPEN; improved exponent OPEN.

Owned scope: `algorithm/paid_cover/` and `results/algorithm-cover-*`. No access to unfinished joint-macro work and no subagents.

The candidate will define a total precut generator, terminal applicability tests,
witness reconstruction, a fallback for every outside state, and the cost of
every emitted child and local query. Test instruments may compute optima but
will never be called by the proposed algorithm.

The first design lens is clearing nonpure degree-three overlap vertices by
multi-color splitting cores. Before testing, freeze the full candidate and
its predicted paid mass. When a smallest measured counterexample kills a
candidate, preserve it and change the organizing approach.

## Universal obligations

- Complete finite state/action specification: OPEN.
- Optimum-preserving precut cover: OPEN.
- Conditional terminal library hypotheses at each call: OPEN.
- Exact fallback and reconstruction: OPEN.
- Termination: OPEN.
- Paid cover generation, query and fallback cost: OPEN.
- Rational bound at some c < 2.3391: OPEN.
- Fresh nonauthor reconstruction and Lean replay: OPEN.

## Evidence ledger

The 27-control battery passed before the pilot. Its first execution stopped
at a suppression fixture's child-order mismatch; the exact representation
was diagnosed and the manually canonical expected tuple corrected. The
failed receipt is preserved as `results/algorithm-cover-controls-failed-01.json`.
No real-input run preceded that stop.

Candidate B1 is inadequate for the unrestricted exponent. The frozen
quartet `T=((0,1),(2,3))`, `F=[((0,2),(1,3))]` emits zero overlap cores.
Its one source color makes pure-bridge membership vacuous, while the sole
unmarked local query has the original four labels and full remaining budget.
The paid safe-cover vector is `[0]`, mass exactly one. Bounded edge search
finds no witness at q=0 or q=1 and reconstructs a three-block witness at q=2.
`results/algorithm-cover-pilot-v1.json` retains the full input, queried budgets,
partition, original-source cut reconstruction, operation counts and timings.
This is development evidence, not independent certification.

The source-realization control also caught the separate payment trap:
target root regions `{0,1}|{2,3}` intersect in source
`((0,2),(1,3))` and admit no one-cut realization. The clean equal-topology
twin does admit one cut. B1 therefore explicitly admits only compatible
touching components and checks each claimed cut realization.

The terminal frontier candidate enumerates source precuts until
compatible/triple membership and accounts for generation and cardinality.
B2 keeps only globally minimum-paid terminal states.
Candidate B2 **failed** on five leaves after 54 compared shape-quotient
pairs, including every one of the 30 four-leaf pairs. Its seven frontier
controls (including the replay of all 27 B1 controls) passed first; a
20-case mixed-size pilot took 0.01513 seconds. The measured projection was
recorded before bounded search. The bounded run took 0.03387 seconds and
stopped at its first exact fire.

The literal parent is
`T=((((3,4),2),1),0)`, `T'=(((1,4),2),(0,3))`.
The two-cut optimum witness is `{0,1,4}|{2}|{3}`. The only distinct
minimum-paid compatible/triple states are:

| Precut label partition | Paid cuts | Exact residual cuts | Total cuts |
|---|---:|---:|---:|
| `{0,3}|{1,2,4}` | 1 | 2 | 3 |
| `{0,2,3}|{1,4}` | 1 | 2 | 3 |

Every cheapest terminal state therefore loses every original optimum.
`results/algorithm-cover-frontier-bounded-v2.json` preserves the parent,
literal witness, all actual one-cut precuts, all child values and witnesses,
and the total solver's explicit original-state fallback that recovers q=2.
The test reference is development cut enumeration with the same graph
primitives; this is not separate-author certification. Smallest means
smallest leaf count in the exhausted shape-quotient family, with the
quotient's unformalized relabeling argument noted in `branching/README.md`.

The B3 generator retains every inclusion-minimal terminal precut across
paid cut counts. This restores
the missing two-cut entry states. Its generator must enumerate all cut
sets within q first, so its exact worst-case cost is charged as a sum of
binomial coefficients, and its retained family is charged without silently
discarding the more expensive states.

## Final retained outcome

B3 supplies a total finite executor and original-source cut reconstruction,
with an explicit fallback for every admitted state. On the five-leaf fire,
it tests 37 precut sets, obtains 17 distinct terminal states, and retains
10 inclusion-minimal terminal states after charging 180 coarsening scans.
The paid vector is `(1,1,2,2,2,2,2,2,2,2)`, with exact mass
`126200/53361 > 1` at 231/100. It recovers the two-cut parent witness without
the original-state fallback. The quartet retains five one-cut states,
mass `500/231 > 1`. These masses reject this particular recurrence
certificate; a one-level terminal cover's mass alone does not rule out
every global charging argument. Its explicit generation/query bounds in
`PIN-v3.md` remain non-FPT, so no improved exponent is supplied.

The final command-line entry point is `state_cli.py`: fixed-budget decision
or iterative-budget optimization, empty/singleton cases included. Its
full-path conflicting-triple plant returns two components and one cut;
the duplicated-label input is rejected. Evidence is retained in
`results/algorithm-cover-cli-controls-v1.json`.

Supplementary controls exercise an actual compatible two-color core with
vector `(1,2)` and a three-color core with vector `(2,3,3)`. The latter
forest has an explicit two-cut original-source certificate. Lower budgets
fail, exact budgets return checked witnesses, and a reduced fake charge
is caught by the stored actual cut certificates. These are synthetic
development states, not hard t=2 reachability or universal m-color coverage.

`FailedFrontier.lean` compiled and its ten statements were audited. In the
existing executable RMAF model, the parent minimum is two cuts and every
bounded feasible assignment refining any one-cut terminal state costs at
least three. The false minimum-frontier preservation theorem is rejected
for its false proposition. The only used axioms are `propext`,
`Classical.choice`, and `Quot.sound`; no sorry/admit/custom axioms or
native_decide occur. `MassChecks.lean` adds four exact integer checks,
including failure of the full-cover vector at the rational benchmark
23391/10000; their axiom lists are empty. The dependency model's graph
correspondence and fresh nonauthor replay remain OPEN.

All three original milestones remain **OPEN**. This route delivers a
measured failed-cover witness and a complete finite candidate with all
costs/fallbacks exposed. It does not deliver an unrestricted improved
algorithm or a novelty claim. The terminal libraries, degree-two release,
and family merge/restriction release were not assumed. See
`CONSUMER-TRACE.md` for every actual and hypothetical consuming interface.

Shared BootLoops suite: not rerun by this child; parent owns any shared run.
No upstream toolkit/verification/pin or prior result was changed. No
external engine or hosting was used. Runtime observations are local pilot
measurements, not scientific acceptance. Fresh graph certification,
universal algorithm/cut correspondence, full runtime proof, and fresh Lean
replay remain pending.

The sandbox did not permit `ps` process inspection during the Lean build.
The retained Lean session completed successfully and its theorem dependency
prints were replayed into the audit logs; no scientific conclusion depends
on process liveness or CPU activity.
