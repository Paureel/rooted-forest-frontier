# Actual second paid selector interface v1

Namespace: `Universal233.Rule5PaidSelector`.
Import `SelectorBuilder` for the executable geometry builder and
`PaidRequests` for the actual full-source-forest query list.

`buildSelected T S a b : Option (SelectedPaid T S)` computes original
`selectFinal`, accepts its `.remaining d (.second u v)` result, enumerates
finite literal source rows and validates original target/source shape
checks. `SelectedPaid` carries d, u, v and the proved
`Case322PaidGuard.LiteralGeometry T S`.

`buildSelected_complete ch ad sel` proves nonrefusal for actual
`CherryAt T i a b`, original `admitted T S a b=true` and actual printed
second selection. No SourceGeometry input occurs. `buildSelected_binding`
retains the selected d/u/v and binds geometry.r=v, geometry.uc=u,
geometry.c=d.c, actual d.badArc X labels and either original endpoint order.
`selected_literal_exists` is the direct proof-only geometry theorem.

`requests R.geometry q : List PaidRequest` emits the literal affordable
paid list. Each record carries its original branch/cuts/partition, the
physical opposite-role target, the entire materialized current source
forest, and residual q minus the full original cut-list length.
`requestFor_binding` gives these equalities for each record.

`full_state_iff`, `full_state_proper`, `full_state_cost`, and
`full_state_paid_budget` establish exact original-label AF/refinement and
budget semantics on either operational role. `selected_full_request_cover`
and `selected_full_request_sound` prove universal affordable coverage and
soundness of this actual list. The original paid guard, list multiplicity,
callback decrease and explicit role transport are inherited through
`SelectorConsumer`; surgery is not re-proved.

The remaining recursive callback call is
`solve (some Q.target) Q.sources Q.residual` for each actual emitted Q.
Its soundness/completeness must hold at that literal residual budget.
This package supplies the actual request and its exact semantic contract;
it does not supply or assume a runtime ghost, minimum callback, global IH
or complete recursive dispatcher. The frozen LocalIH/source-pool releases
were not imported, and parent generic bindings were not duplicated.

Fresh independent review and parent integration remain pending. All three
main algorithm milestones and novelty remain OPEN. q=k-1; no implicit rho.
