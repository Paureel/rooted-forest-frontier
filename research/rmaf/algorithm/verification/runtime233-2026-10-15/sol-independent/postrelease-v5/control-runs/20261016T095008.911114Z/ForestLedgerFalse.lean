import ForestArmBinding
open RMAF Universal233.Rule5SelectedLocalWork
private def c : Universal233.CherryBranching.Child := ⟨[[0]],[.leaf 0],1⟩
example : (childrenAnswersMeter (fun _ _ _=>none) (fun _=>5) (.leaf 0) 3 [c,c,{c with paid:=4}]).recursiveWork=5 := by decide +kernel
