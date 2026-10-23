import RWRefusals
open RMAF Universal233.CoreProgram OrdinaryDispatch.RecoveryLocalWork
private def g (p : Vertex) (x color : Nat) : GTree := .leaf ⟨p,[x],color⟩
private def mixed : GTree := .node [] (.node [false] (g [false,false] 0 0) (g [false,true] 1 1)) (.node [true] (g [true,false] 2 0) (g [true,true] 3 1))
example : (meterRun 0 mixed [] []).value.childAttempts=1 := by decide +kernel
