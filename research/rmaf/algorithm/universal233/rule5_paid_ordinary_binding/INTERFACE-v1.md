# Actual second bounded ordinary interface v1

Namespace `Universal233.Rule5PaidOrdinary`. Import `SelectedExact`.

`currentQuery actual T ss r : CurrentResult` distinguishes malformed state
from answered none/some forest. It uses exact full-state cost0/1 pretesting
and falls back to unchanged GenericForest.solve actual only after rejection
at r≥2. `currentQuery_sound` is unconditional; `currentQuery_minimum` and
`currentQuery_complete` consume LocalOrdinaryIH r actual. They give global
minimum length and completeness for the fixed actual full-state query.
`currentQuery_malformed_iff` is exactly original ForestState.proper=false.

`BelowIH q actual` abbreviates ∀r,r<q → LocalOrdinaryIH r actual.
`selected_paid_positive`, `request_decrease`, and `request_payment_exact`
prove positive full originalCuts payment, actual residual<q and exact
residual+full payment=q. `request_not_malformed` discharges the explicit
malformed outcome on every actual emitted proper request.

`answers actual R q` evaluates every affordable actual PaidRequests
occurrence and flattens returned forests. `bestFor` retains only original
q-feasible agreement forests and chooses minimum length. `solveSelected
actual T S a b q : SelectedResult` distinguishes builderRefused from
answered none/some forest.

`solveSelected_sound` is unconditional. `solveSelected_minimum` consumes
only BelowIH q actual and gives a global original minimum for any returned
forest. `solveSelected_complete` consumes the actual cherry, admitted
guards, actual printed `.remaining d (.second u v)` selection and BelowIH,
and returns a forest no longer than any original q-feasible witness.
`actual_second_feasible_iff` gives exact bounded feasibility.
`actual_second_never_builder_refuses` proves builder refusal impossible
only after the actual selected-second hypotheses are supplied.

Role swapping keeps the same original cuts, source forest and payment via
the inherited literal operational binding. Every actual three/four-or-more
original cut is paid by list length; no hard-child discount is assumed.
No global ordinary IH, runtime ghost, minimum callback or optimum oracle
is part of the new executable program.

Verification boundary is recorded in RESOURCE-STOP-20261015T1918Z.md until
controls and a new-module-only audit run with a restored stable reserve.
All main algorithm milestones, novelty and independent acceptance remain
OPEN.
