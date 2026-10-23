import ForestArmBinding
open RMAF Universal233.Rule5SelectedLocalWork
private def c : Universal233.CherryBranching.Child := ⟨[[0]],[.leaf 0],1⟩
private def no : Ordinary := fun _ _ _=>none
example : (childExecutionMeter no (fun _=>5) (.leaf 0) 3 c).calls.length=1 := by decide +kernel
example : (childExecutionMeter no (fun _=>5) (.leaf 0) 3 c).recursiveWork=5 := by decide +kernel
example : ((childExecutionMeter no (fun _=>5) (.leaf 0) 3 c).calls.map (fun j=>j.budget))=[2] := by decide +kernel
example : (childrenAnswersMeter no (fun _=>5) (.leaf 0) 3 [c,c,{c with paid:=4}]).calls.length=2 := by decide +kernel
example : (childrenAnswersMeter no (fun _=>5) (.leaf 0) 3 [c,c,{c with paid:=4}]).recursiveWork=10 := by decide +kernel
example : (childrenAnswersMeter no (fun _=>5) (.leaf 0) 3 [c,c,{c with paid:=4}]).localWork=22 := by decide +kernel
example : (bestLengthMeter (fun _=>⟨true,2⟩) [[[9]],[]]).value=some [] := by decide +kernel
example : (bestLengthMeter (fun _=>⟨true,2⟩) [[[9]],[]]).work=14 := by decide +kernel
