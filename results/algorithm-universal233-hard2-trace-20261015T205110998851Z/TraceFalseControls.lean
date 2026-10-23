import TraceControls
open RMAF Universal233 Universal233.BothBad OrdinaryDispatch.Hard2Trace.Controls
example : traceMass 2 4 failedCalls=1/8 := by cbv
example : traceMass 2 4 [⟨some (.leaf 0),[.leaf 0],1⟩]=1/4 := by cbv
example : 1≤2*(233/100 : Rat)^(-1 : Int)+4*(233/100 : Rat)^(-4 : Int) := by cbv
example : 2*(2 : Rat)^(-1 : Int)+4*(2 : Rat)^(-4 : Int)<1 := by cbv
