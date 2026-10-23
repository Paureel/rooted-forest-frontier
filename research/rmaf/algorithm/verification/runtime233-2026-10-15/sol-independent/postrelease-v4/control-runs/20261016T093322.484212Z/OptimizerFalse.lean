import OWOptimize
open RMAF Universal233.WholeSourceWork OrdinaryDispatch.OptimizerLocalWork
private def query (q : Nat) : Charged (Option (List (List Nat))) := ⟨if q=1 then some [[7]] else none,5⟩
example : (meterScan query 0 4).work=17 := by decide +kernel
