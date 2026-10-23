-- New interface trap; previously passed static/generic controls are reused.
import ForwardCallerR3
import SelectedInstance10
open RMAF Universal233 OrdinaryDispatch
namespace ContactedForwardCallbacks

def zeroCostBranch : Rule4.Branch := ⟨.leaf 0,.leaf 0,[],false⟩
theorem zero_cost_trap : zeroCostBranch.cost≤0 ∧ 0-zeroCostBranch.cost=0 ∧ ¬0<0 := by decide
example {T S : Tree} (s : Rule4.Choice T S) (b : Rule4.Branch)
 (member : b∈Rule4.branches s) (q : Nat) (affordable : b.cost≤q) : q-b.cost<q :=
 (ContactedForward.actual_callback_budget s member affordable).1
end ContactedForwardCallbacks
#check PaidInstances.local_ordinary_ih
#check PaidInstanceForest.forest_completion_obligation
#check GenericForest.solve_sound
#check ContactedForward.emitted_materialized_scope
#check ContactedForward.checked_forward_caller

-- Author integration type/axiom reports; proof text above is unchanged apart from recorded import edits.
set_option pp.universes true
#check @ContactedForwardCallbacks.zero_cost_trap
#print axioms ContactedForwardCallbacks.zero_cost_trap
