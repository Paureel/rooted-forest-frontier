import FinalControls
namespace Universal233.Rule5SourceOrientation.Controls
open RMAF CoreGraph Integration VertexGeometry CutRealization HardParent CherryBranching Rule5Local Rule5Classification Rule5FinalClassification
example : fork true (.leaf 0) (.leaf 1) = .node (.leaf 1) (.leaf 0) := by decide
example : fork false (.leaf 0) (.leaf 1) = .node (.leaf 0) (.leaf 1) := by decide
example : (leaves (fork true (fork false (.leaf 0) (.node (.leaf 3) (.leaf 4))) (.leaf 2))).contains 4 = true := by decide
example : (splitForest (splitForest [[0,1],[2],[3,4]] [3,4]) [2]).length = 3 := by decide
end Universal233.Rule5SourceOrientation.Controls
