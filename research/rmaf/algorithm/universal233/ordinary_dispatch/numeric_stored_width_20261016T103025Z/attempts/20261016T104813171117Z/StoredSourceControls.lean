import StoredControls
namespace OrdinaryDispatch.StoredNumeric.Controls
open RMAF

def simple : RMAF.Tree:=.node (.leaf 1) (.leaf 2)
theorem actual_builder_markers :
 ((OrdinaryCommonSplit.Source.buildSetup simple simple [1] [2] [false]).map (fun d=>(d.rho,d.gamma))).getD (0,0)=(3,4) := by cbv
end OrdinaryDispatch.StoredNumeric.Controls
