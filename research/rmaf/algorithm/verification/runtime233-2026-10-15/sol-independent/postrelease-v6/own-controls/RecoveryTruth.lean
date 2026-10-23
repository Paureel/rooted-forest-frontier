import RWRefusals
open RMAF Universal233 Universal233.CoreProgram Universal233.WholeSourceWork OrdinaryDispatch.RecoveryLocalWork
private def leafGroup (p : Vertex) (x color : Nat) : GTree := .leaf ⟨p,[x],color⟩
private def t : Tree := .node (.leaf 0) (.leaf 1)
private def dup : Tree := .node (.leaf 0) (.leaf 0)
private def color (x : Nat) : Charged Nat := ⟨x+9,5⟩
private def same : GTree := .node [] (leafGroup [false] 0 7) (leafGroup [true] 1 7)
private def mixed : GTree := .node [] (.node [false] (leafGroup [false,false] 0 0) (leafGroup [false,true] 1 1)) (.node [true] (leafGroup [true,false] 2 0) (leafGroup [true,true] 3 1))
example : (meterGroups same).value.length=2 := by decide +kernel
example : (meterGroups same).work=20 := by decide +kernel
example : (meterNormalize same).work=28 := by decide +kernel
example : (meterNormalize same).value=GTree.leaf ⟨[],[0,1],7⟩ := by decide +kernel
example : (meterBuild color [] t).work=42 := by decide +kernel
example : (meterBuild color [] t).coloring=10 := by decide +kernel
example : (meterInitial color 100 t).value.map Prod.fst=some 1 := by decide +kernel
example : (meterInitial color 100 dup).coloring=0 := by decide +kernel
example : (meterRun 0 mixed [] []).value.childAttempts=2 := by decide +kernel
example : (meterRun 0 mixed [] []).value.outputs.length=0 := by decide +kernel
example : (meterColor [[],[2,3],[4]] 3).value=2 := by decide +kernel
example : (meterRecover (.leaf 0) [[0]]).value.isSome=true := by decide +kernel
example : (meterRecover dup [[0]]).value.isNone=true := by decide +kernel
example : (2:Rat)^3<(233/100:Rat)^3 := by decide +kernel
