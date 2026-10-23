import CommonControls
namespace Universal233.Rule5CommonSelector.FalseControls
open RMAF CoreGraph Integration VertexGeometry CutRealization HardParent CherryBranching Rule5Local Rule5Local.Pre Rule5Classification Rule5Classification.Controls Rule5FinalClassification Rule5FinalClassification.Controls Rule5CommonSelector.Controls
set_option maxRecDepth 10000
example : DepthOne.vertices (.node (.leaf 0) (.leaf 1))=[[],[true],[false]] := by decide
example : OrdinaryCommonSplit.Source.incident commonT (subtreeLabels commonS commonD.badArc)=[[]] := by decide
example : OrdinaryCommonSplit.Source.incident rootT (subtreeLabels commonS commonD.badArc)=[[false]] := by decide
example : 2∈coreLabels commonS 0 1 := by decide
example : (commonJobs commonT commonS 0 1 commonD 5).isEmpty=true := by decide
example : (commonJobs commonT commonS 0 1 commonD 5).all (fun j => j.budget==5)=true := by decide
end Universal233.Rule5CommonSelector.FalseControls
