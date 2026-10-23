import OWOptimize
open RMAF Universal233.WholeSourceWork OrdinaryDispatch.OptimizerLocalWork
private def query (q : Nat) : Charged (Option (List (List Nat))) := ⟨if q=1 then some [[7]] else none,5⟩
example : (meterScan query 0 4).value.trials.length=2 := by decide +kernel
example : (meterScan query 0 4).value.selected=some (1,[[7]]) := by decide +kernel
example : (meterScan query 0 4).work=34 := by decide +kernel
example : (meterScan query 0 4).administration=24 := by decide +kernel
example : (meterScan (fun _=>⟨none,5⟩) 0 2).work=36 := by decide +kernel
example : (meterScan query 0 0).work=2 := by decide +kernel
example : (meterLength [10,20,30]).work=14 := by decide +kernel
example : (meterFinish (.leaf 0) ⟨none,[]⟩).work=8 := by decide +kernel
example : preflightFee 1=1024 := by decide +kernel
