import BindingControls
namespace Universal233.Rule5CommonOrdinary.FalseControls
open RMAF CoreGraph Integration VertexGeometry CutRealization HardParent CherryBranching Rule5Local Rule5Local.Pre Rule5Classification Rule5Classification.Controls Rule5FinalClassification Rule5FinalClassification.Controls Rule5CommonSelector Rule5CommonSelector.Controls
set_option maxRecDepth 10000
example : (some (some [[0,1],[2]]) : Option (Option (List (List Nat)))).join=none := by decide
example : (some none : Option (Option (List (List Nat)))).join=some [[0]] := by decide
example : (commonJobs commonT commonS 0 1 commonD 5).all (fun j => j.budget==5)=true := by decide
example : (commonJobs commonT commonS 0 1 commonD 5).all (fun j => 5-j.budget==0)=true := by decide
example : runSelectedCommon (fun _ _ _ => none) commonT commonS 0 1 commonD 5=some [[0]] := by decide
end Universal233.Rule5CommonOrdinary.FalseControls
