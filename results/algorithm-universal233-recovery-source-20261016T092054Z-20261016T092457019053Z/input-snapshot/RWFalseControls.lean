import RWControls
namespace OrdinaryDispatch.RecoveryLocalWork.Controls
open RMAF Universal233 WholeSourceWork CoreWork CoreProgram
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000
example : (2:Nat)+3=6 := by decide
example : (meterGroups (.leaf g7)).work=0 := by decide
example : (meterNormalize same).value=.leaf ⟨[],[7],7⟩ := by decide
example : (meterErase [] two).value.isSome=true := by decide
example : (meterRun 0 four [] []).value.pruned=0 := by decide
example : (meterRun 1 four [] []).value.visited=1 := by decide
example : (meterRun 2 four [] []).value.outputs.length=1 := by decide
example : (meterAttempt marker two [] [] ⟨[],[9],9⟩).work=0 := by decide
example : (meterBuild paidColor [] (.leaf 7)).coloring=0 := by decide
example : (meterInitial paidColor 1000 repeated).coloring=11 := by decide
example : (meterRecover (.leaf 7) [[7]]).value.map (fun o=>o.sourceCuts.length==o.partition.length)=some true := by decide
example : localCap 0=CoreWork.cap 0 := by decide
end OrdinaryDispatch.RecoveryLocalWork.Controls
