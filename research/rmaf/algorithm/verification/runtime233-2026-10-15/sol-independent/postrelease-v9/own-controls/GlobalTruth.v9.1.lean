import OptimizerSourceUniform
open RMAF Universal233.WholeSourceWork OrdinaryDispatch.GlobalSourceAssembly OrdinaryDispatch.BudgetOptimization OrdinaryDispatch.OptimizerLocalWork
private def t : Tree := .leaf 0
example : (sourceFinishMeter t ⟨none,[]⟩).work=8 := by decide +kernel
example : (sourceFinishMeter t ⟨none,[]⟩).value.recoveries.length=0 := by decide +kernel
example : (sourceFinishMeter t ⟨some (0,[[0]]),[]⟩).value.recoveries.length=1 := by decide +kernel
example : (meterScan (fun b=>⟨if b=2 then some [[0]] else none,7⟩) 0 5).value.trials.length=3 := by decide +kernel
example : trialWork (fun _=>7) (meterScan (fun b=>⟨if b=2 then some [[0]] else none,7⟩) 0 5).value.trials=21 := by decide +kernel
example : (sourceOptimizeMeter (fun _=>0) t t).value=(sourceOptimizeMeter (fun _=>7) t t).value := by exact (sourceOptimizeMeter_value _ _ _).trans (sourceOptimizeMeter_value _ _ _).symm
example : (meterScan (fun (_ : Nat)=>⟨some [[0]],7⟩) 0 1).work=(meterScan (fun (_ : Nat)=>⟨some [[0]],0⟩) 0 1).work+7 := by decide +kernel
