import OptimizerAssemblyControls
namespace OrdinaryDispatch.GlobalSourceAssembly.OptimizerControls
open RMAF Universal233 OrdinaryDispatch.BudgetOptimization
example : (scan firstAtOne 0 3).trials=[(0,none)] := by decide +kernel
example : (scan alwaysFails 0 3).trials.length=2 := by decide +kernel
example : (finish (.leaf 0) ⟨some (0,[[0]]),[(0,some [[0]])]⟩).recoveries.length=2 := by decide +kernel
end OrdinaryDispatch.GlobalSourceAssembly.OptimizerControls
