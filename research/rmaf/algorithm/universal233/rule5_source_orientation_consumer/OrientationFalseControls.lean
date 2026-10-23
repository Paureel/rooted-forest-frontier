import FinalControls
namespace Universal233.Rule5SourceOrientation.FalseControls
open RMAF CoreGraph Integration VertexGeometry CutRealization HardParent CherryBranching Rule5Local Rule5Classification Rule5FinalClassification
example : fork true (.leaf 0) (.leaf 1) = .node (.leaf 0) (.leaf 1) := by decide
example : fork false (.leaf 0) (.leaf 1) = .node (.leaf 1) (.leaf 0) := by decide
example : (splitForest [[0,1,2]] [1]).length = 1 := by decide
end Universal233.Rule5SourceOrientation.FalseControls
