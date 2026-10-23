-- Exact pre-instance controls; no finite-handler implementation is repeated.
import OneCallerBoundary
import ForestSkinny06
open RMAF OrdinaryDispatch Universal233 Universal233.CherryBranching
namespace PaidInstances
abbrev OrdinarySolver := Nat→Tree→Tree→Option CommonForest
def OwnPaid (ordinary : OrdinarySolver) (q : Nat) : Tree→Tree→Nat→Option CommonForest :=
 fun u v r=>if r<q then ordinary r u v else none
def BelowBudget (ordinary : OrdinarySolver) (q : Nat) : Prop :=
 ∀r,r<q→∀T S,DepthOne.proper T S=true→QueryExact T S r (ordinary r T S)
def zeroChild : Child := makeChild (.leaf 0) [[0]] 0
theorem zero_paid_trap : remaining 0 zeroChild=some 0 ∧ ¬0<0 := by decide
example (ordinary : OrdinarySolver) (q : Nat) (T S : Tree) : OwnPaid ordinary q T S q=none := by simp [OwnPaid]
example (q r : Nat) (c : Child) (positive : 1≤c.paid) (rem : remaining q c=some r) : r<q :=
 IndependentPaid.remaining_strict positive rem
end PaidInstances
#check IndependentPaid.CurrentChildren
#check ContactedOneConsumer.checked_one_caller
#check PaidInstanceForest.forest_completion_obligation

-- Author integration type/axiom reports; proof text above is unchanged apart from recorded import edits.
set_option pp.universes true
#check @PaidInstances.zero_paid_trap
#print axioms PaidInstances.zero_paid_trap
