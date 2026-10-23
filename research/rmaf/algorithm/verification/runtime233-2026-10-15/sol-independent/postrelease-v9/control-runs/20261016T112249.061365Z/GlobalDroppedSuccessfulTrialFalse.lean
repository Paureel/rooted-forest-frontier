import OptimizerSourceUniform
open RMAF Universal233.WholeSourceWork OrdinaryDispatch.GlobalSourceAssembly OrdinaryDispatch.BudgetOptimization OrdinaryDispatch.OptimizerLocalWork
example : trialWork (fun _=>7) (meterScan (fun b=>⟨if b=2 then some [[0]] else none,7⟩) 0 5).value.trials=14 := by decide +kernel
