# Local consuming interface

All public declarations below use namespace `Universal233.CherryBranching`.
The original checker is `RMAF.agreement`; trees are ordinary rooted binary
syntax with distinct original labels and equal original label sets. No rho
label or original cut-subset condition is assumed.

| Call | Delivered hypotheses and result |
|---|---|
| `cherries_sound`, `cherries_complete`, `selected_actual` | Exact original parent/endpoint addresses; selected cut list equals actual opposite-source pendant edges |
| `selected_spec` | Common before t1, t1 before high, high before hard2; all rejected candidates included in the corresponding universal count conditions |
| `actual_high_safety` | Original agreement, proper S, actual target cherry, t>=3; singleton a OR b OR original F refines literal pendantPartition |
| `actual_t1_pendant_exchange` | Proper original T/S, equal labels, original agreement, actual cherry, t=1; constructs original G with |G|<=|F| and G refines literal pendantPartition |
| `actual_t1_target` | Universal t1 source statement; no open exchange premise |
| `endpoint_literal`, `endpoint_components` | Executable actual original leaf cut, exact cost1, isolated leaf/root remainder and no leafless component |
| `high_literal`, `pendant_paid` | Executable original pendant list, literal child state, exact cost t and partition count t+1 |
| `forest_length` | Every checked nonempty block produces an actual restriction, so literal sourceForest has exactly P.length components |
| `paid_budget_identity` | Actual source partition and embeddings, paid+1=P.length, original child agreement/refinement; paid+(|F|-|P|)=|F|-1 |
| `remaining_correct` | Executable remaining budget success/refusal iff the residual child objective has the corresponding original budget |
| `actual_high_budget` | Original decision iff one literal high child succeeds with its actual remaining budget |
| `actual_t1_two_budget` | Original decision iff one of the two cost1 children succeeds |
| `actual_t1_decision` | Original decision iff the deterministic cost1 pendant child succeeds |
| `ordinary_minimum`, `actual_t1_two_minimum`, `actual_t1_deterministic_minimum` | Minimum of explicitly child-specific exact solutions is the original minimum |
| `high_child_solver_iff`, `t1_child_solver_iff` | Executable childCall; ExactBoundedChild IH per concrete child, including refusal/completeness and exact minimum guarantees |

`makeChild S P paid` contains the literal partition P and `P.filterMap
(restrict · S)`. `feasible T S child F` means the original agreement together
with original-label refinement of P. For checked P with actual source
embeddings, completed `OutputState.agrees_iff_original` proves this is exactly
the ordinary current-forest checker on the materialized sourceForest. The t1
proof imports and uses both directions of this equivalence; source separation
is proved here rather than assumed by an original safety theorem.

`ExactBoundedChild T S solver c` is the explicit child IH. For every remaining
budget r, solver c r succeeds iff ChildWithin holds; every returned G is an
exact minimum for this particular child's original agreement/refinement
problem and meets its residual budget. `childCall` first evaluates remaining
and refuses unpaid children. The local theorems do not supply solver.

For final certificate recovery, pass the selected original agreement G to the
completed `Universal233.FinalCutRecovery.recover_original_agreement T S G`.
It returns literal original source cut addresses, exact |G|-1 cut cost,
original residual realization, and an agreement equivalent up to block/label
order. Invoke it once after choosing G; do not union display-edge lists from
children. The source work bound for that call is the completed final recovery
bound. This package imports the completed output-state/common-cherry proof
chain; final recovery is a separate already-completed consuming call.

First remaining mathematical consumer outside this local package: construct a
complete exact recursive solver satisfying ExactBoundedChild for every actual
child state, including the separate hard2/special-priority cases and global
termination. No local cherry claim is left open.
