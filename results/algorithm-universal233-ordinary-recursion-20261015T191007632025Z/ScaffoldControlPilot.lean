import ScaffoldExact
namespace OrdinaryScaffold.ControlPilot
open RMAF

def T : Tree := .node (.node (.leaf 0) (.leaf 1)) (.node (.leaf 2) (.leaf 3))
def S : Tree := .node (.node (.leaf 0) (.leaf 2)) (.node (.leaf 1) (.leaf 3))
theorem actual_found : (solve 2 T S).map (fun F=>(agreement T S F,F.length))=some (true,3) := by cbv
end OrdinaryScaffold.ControlPilot
