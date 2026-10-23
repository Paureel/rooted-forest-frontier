import OWBudgets
import RWInterface
namespace OrdinaryDispatch.GlobalSourceAssembly.OptimizerControls
open RMAF Universal233 OrdinaryDispatch.BudgetOptimization

def firstAtOne (q : Nat) : Option CommonForest:=if q=1 then some [[0]] else none
def alwaysFails (_ : Nat) : Option CommonForest:=none

theorem success_prefix_literal :
 (scan firstAtOne 0 3).trials=[(0,none),(1,some [[0]])] ∧
 (scan firstAtOne 0 3).selected=some (1,[[0]]) := by cbv

theorem all_failed_prefix_literal :
 (scan alwaysFails 0 3).trials=[(0,none),(1,none),(2,none)] ∧
 (scan alwaysFails 0 3).selected=none := by cbv

theorem final_recovery_occurrences :
 (finish (.leaf 0) ⟨none,[]⟩).recoveries.length=0 ∧
 (finish (.leaf 0) ⟨some (0,[[0]]),[(0,some [[0]])]⟩).recoveries.length=1 := by cbv
end OrdinaryDispatch.GlobalSourceAssembly.OptimizerControls
