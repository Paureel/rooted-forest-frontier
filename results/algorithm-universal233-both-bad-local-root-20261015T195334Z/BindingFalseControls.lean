import BindingControls
namespace Universal233.BothBadLocal.Controls
open RMAF BothBad BothBad.Precontrols
set_option maxRecDepth 10000
example : (ordinaryExecution lowF T S [leaves S] 3).answer=(ordinaryExecution lowG T S [leaves S] 3).answer := by decide
example : (ordinaryExecution lowF T S [leaves S] 2).answer=none := by decide
example : (plan S T A B C (PairGeometry.descendants T edge.2) 5).map (fun e=>e.mode.extra)=[0,0,0] := by decide
example : (runPair malformedActual S T A B C edge 0).answer=some [[999]] := by decide
example : agreement (.leaf 0) (.leaf 0) [[999]]=true := by decide
end Universal233.BothBadLocal.Controls
