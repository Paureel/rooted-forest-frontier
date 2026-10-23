import OWControls
namespace OrdinaryDispatch.OptimizerLocalWork.Controls
open RMAF Universal233 WholeSourceWork CoreWork OrdinaryDispatch.EarlyLocalWork OrdinaryDispatch.BudgetOptimization
example : (2:Nat)+3=6 := by decide
example : sscan.work=26 := by decide
example : trialWork (fun q=>(synthetic q).work) sscan.value.trials=2 := by decide
example : fscan.value.trials=[] := by decide
example : (meterScan synthetic 0 0).value.selected.isSome=true := by decide
example : (meterLength ([0,1,2]:List Nat)).work=0 := by decide
example : (meterPreflight malformed malformed).work=0 := by decide
example : (meterInputCheck (.leaf 7) (List.replicate 40 [7])).value=true := by decide
example : (meterOptimize (fun _=>0) (.leaf 7) (.leaf 7)).value.recoveries.length=0 := by decide
example : (meterRecovery (.leaf 7) [[7]]).value.map (fun o=>o.sourceCuts.length==o.partition.length)=some true := by decide
end OrdinaryDispatch.OptimizerLocalWork.Controls
