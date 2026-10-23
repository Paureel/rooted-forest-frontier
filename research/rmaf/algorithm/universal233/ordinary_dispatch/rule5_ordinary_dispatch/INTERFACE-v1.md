# Actual admitted Rule5 handler interface v1

Import `SelectedInterfaces` from the canonical replay named in the final
manifest. The runtime namespace is `Universal233.Rule5OrdinaryDispatch`.

`dispatch actual T S a b q` evaluates the frozen `selectFinal T S a b` and
executes its literal result. Its result type distinguishes `selectorRefused`,
`paidBuilderRefused`, and `answered (Option Forest)`. No geometry, minimum,
coverage witness or mathematical completion is a runtime argument.

The sole recursive correctness input is `BelowIH q actual`, defined as
`forall r, r < q -> LocalOrdinaryIH r actual`. The original inputs are a
target cherry `CherryAt T i a b` and the printed `admitted T S a b = true`.
The handler derives selector soundness and every branch cover from these
actual guards. It does not take a global `SourceIH` or desired cover premise.

`admitted_exact` proves an answered result and `ExactAnswer` for that result.
`admitted_sound_minimum` proves original agreement, original cost at most q,
and minimum length among **all** original agreement forests. Completeness
holds for every original q-feasible forest through `admitted_complete`.
`admitted_feasible_iff` and `admitted_none_iff` give the bounded decision
contract. `admitted_never_refuses` excludes both refusal constructors.

The large, size-two and outside prefix executes the original literal child
lists. Large uses the proved source exchange; the other two use all five
children. First and third use the actual saved orientation and endpoint,
including the endpoint swap. Each affordable child calls
`GenericForest.solve actual (some T) c.sourceForest (q-c.paid)` once per list
occurrence. The concrete adapter is `OrdinaryDispatch.forestChild` and its
contract is instantiated only at that residual. The minimum is selected from
returned candidates after checking original agreement and original q-budget.

Common.one invokes frozen `runSelectedCommon`; its scoped common-source IH
is derived from BelowIH in the completed dependency. Paid.second invokes
frozen `solveSelected`, including its full-current-forest pretest resolver,
full original cut list, role transport and explicit builder refusal. Its
nonrefusal follows from the actual selected second case.

`answers_are_literal_queries` identifies the child evaluator with the stored
whole-forest query list. `selected_forest_job_binding` proves literal target,
permanent partition, full materialized source forest, original source checks,
valid nonroot distinct original cuts, full cut-count payment and residual<q.
`selected_forest_callback_locality` proves that each forest query observes
only smaller-budget ordinary callbacks, using the unchanged forest program's
proved budget locality. `common_one_job_binding` gives actual proper ordinary
jobs with drop one; `second_request_binding` gives actual proper full-source
paid requests with their exact full original-cut drop.

`selected_forest_vectors` retains [2], [2,2,2,2,2], or [1,2] as appropriate;
unaffordable requests are omitted by the actual remaining-budget test. The
job lists retain repeated occurrences. `job_weight_is_full_paid` identifies
the exponent q-residual with the complete source payment for each emitted
forest job. It is a debit identity, not a bound on the inner ordinary call
mass. The common and paid request interfaces retain their frozen concrete
jobs rather than replacing them with these forest-child vectors.

No functional source call remains unproved within admitted Rule5. The next
functional consumer is the total ordinary dispatcher and its actual priority
proof. The full source-operation, label/payload-growth and bit recurrence,
including inner forest-query mass, remain open. No improved base or main
algorithm acceptance follows from this component.
