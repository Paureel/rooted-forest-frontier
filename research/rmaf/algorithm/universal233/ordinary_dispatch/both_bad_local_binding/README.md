# Budget-local actual BothBad binding

Author release; independent review pending. `runPair` is literally
`BothBad.solvePair (GenericForest.solve actual)`. Its plan, answers and call
lists are the completed runtime's original values. The only runtime callback
is actual. No completion or minimum oracle appears in the executable body.

`solvePair_conditional_cover` and `solvePair_minimum` require only
`BelowIH q actual = forall r<q,LocalOrdinaryIH r actual` for recursive
correctness. Their other hypotheses are the original source/target geometry:
proper same-label trees, the literal checked source partition and embeddings,
A/B bad, C good, actual PairGeometry edge choice and outside-parent clearance.
Every original parent-refining agreement within q is covered by a returned
agreement no larger than it. Any returned answer is minimum among all original
parent-refining agreements. The surrounding hard2 dispatcher retains its
two endpoint alternatives; this local minimum is not a full algorithm claim.

`plan_entry_budget_drop` proves `e.budget+3<=q` for every literal planned
entry, including entries that produce no callback. It uses the original
plan budget equation, actual generated source lists, selected rank 4 and
generate_color_cost. No source cuts or retained-mode extra are refunded.
`solvePair_calls_strict` retains the actual call list and proves each recorded
callback budget is strictly below q. `solvePair_trace_mass` consumes the
existing actual forest-callback trace bound `4*c^-4` for `2<=c<=3`, including
failed calls. Expansion of forest-query work and the full cost recurrence
remain separate main obligations.

The proof obtains a mathematical ordinary extension only as erased support.
It retains the actual callback on ALL inputs below q, including malformed
pairs. GenericForest callback locality and ordinary scheduler answer locality
then identify the actual answers with the proof execution. The empty q=0
range is supported without assuming any ordinary IH at budget 0. No global
OrdinaryIH or ExactSolverHyp is an external premise of the local cover or
minimum interfaces.

Reusable generic interfaces in namespace Universal233.BothBadLocal:

- ordinaryExecution_answer_congr_at: pointwise ForestSolver equality on all
  target/source inputs at budgets <=K transfers the answer for b<=K.
- ordinary_candidate_local: the completed ordinary query caller with actual
  GenericForest.solve needs only LocalOrdinaryIH b actual.
- ordinary_candidate_below: the same caller from BelowIH q actual and b<q.
- forest_exact_at_local: the original forest ExactAt at a bounded query.

The canonical five-module audit retained 60 new stored occurrences and only
Classical.choice, Quot.sound and propext in the AX union. Full nonproof bodies
and actual theorem proof references/AX closure are retained. All 169 dependency
source/olean pairs match frozen origins and the final frozen fast pool; none
was rebuilt or altered. Nine false budget/locality controls were rejected.
The wrong-budget control explicitly shows that equality through budget 2
cannot be extended to an ordinary query at budget 3. All failures remain.

All complete-algorithm, correctness, base-case, recurrence, runtime and
novelty milestones remain OPEN. Independent credit is 0. The conditional
c=2.33 target, initial q=k_opt-1 and absence of implicit rho are unchanged.
