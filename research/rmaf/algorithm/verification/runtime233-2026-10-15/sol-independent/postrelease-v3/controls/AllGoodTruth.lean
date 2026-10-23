import Polynomial
open RMAF AllGoodDP AllGoodDP.LocalWork Universal233.WholeSourceWork
set_option maxRecDepth 100000
namespace OwnPhase3
private def fee (n : Nat) : Charged Nat :=
 ⟨if n=0 then 2 else if n=1 then 1 else 3,if n=0 then 5 else if n=1 then 7 else 11⟩
private def paint : Paint := .node 0 (.leaf 1 0) (.leaf 2 1)
private def rawEmpty : Paint := .node 0 (.leaf 1 1) (.leaf 2 1)
example : (meterBest fee [0,1,2]).value=some 1 ∧ (meterBest fee [0,1,2]).work=66 := by decide +kernel
example : (meterBest fee [2]).work=12 := by decide +kernel
example : (meterBest fee []).work=4 := by decide +kernel
example : (meterBest fee [0,0,0]).work=56 := by decide +kernel
example : (meterChanges paint).value=1 ∧ (meterChanges paint).work=24 := by decide +kernel
example : (meterEdgeCost 1 paint).value=2 ∧ (meterEdgeCost 1 paint).work=32 := by decide +kernel
example : (meterSplit rawEmpty).work=44 ∧ (meterBlocks rawEmpty).value=[[1],[2]] ∧ (meterBlocks rawEmpty).work=80 := by decide +kernel
example : (meterTable [0,0] (fun _=>⟨0,0⟩) (.node (.leaf 1) (.leaf 2))).value.length=2 := by decide +kernel
example : (meterTable [] (fun _=>⟨0,0⟩) (.node (.leaf 1) (.leaf 2))).value.length=0 := by decide +kernel
example : (meterNonempty [[],[1],[]]).value=[[1]] ∧ (meterNonempty [[],[1],[]]).work=28 := by decide +kernel
end OwnPhase3
