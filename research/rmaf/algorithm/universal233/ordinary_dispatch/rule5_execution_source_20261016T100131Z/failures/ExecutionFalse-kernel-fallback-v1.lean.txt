import ExecutionControls
namespace Universal233.Rule5ExecutionSource
open RMAF Rule5PrefixLocalWork Rule5SelectedLocalWork
open OrdinaryCommonSplit.Caller
example : (jobsAnswersMeter cbNone W [⟨t2,t2,0⟩,⟨t2,t2,0⟩]).recursiveWork=17 := by decide
example : (bestAdditionalMeter [.leaf 0] (fun _=>⟨true,1⟩) [[[0]],[]]).value=some [] := by decide
example : (currentQueryMeter cbNone W13 (some crossT) [crossS] 2).ordinaryCalls=[] := by decide
example : (splitForestMeter [0] [[],[0,1,0],[2]]).value=[[],[0,0],[1],[2]] := by decide
example : (currentGuardMeter t2 t2 dup).value=true := by decide
example : (arcPartitionMeter t2 [[false],[false]]).work=(arcPartitionMeter t2 [[false]]).work := by decide
example : (requestListMeter t2 t2 1 [c,c]).value.length=1 := by decide
example : (natListEqMeter [0,0] [0]).value=true := by decide
end Universal233.Rule5ExecutionSource
