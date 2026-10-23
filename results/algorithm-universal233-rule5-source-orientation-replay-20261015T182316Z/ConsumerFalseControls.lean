import ConsumerControls
namespace Universal233.Rule5SourceOrientation.FalseControls
open RMAF CoreGraph Integration VertexGeometry CutRealization HardParent CherryBranching Rule5Local Rule5Local.Pre Rule5Classification Rule5Classification.Controls Rule5FinalClassification Rule5FinalClassification.Controls Rule5SourceOrientation.Controls
set_option maxRecDepth 10000
example : firstChildren firstS 0 1 firstD=[singletonChild firstS 1,pendantChild firstS 0 1] := by decide
example : thirdChildren thirdS 0 1 thirdD=[singletonChild thirdS 0,pendantChild thirdS 0 1] := by decide
example : (firstChildren firstS 0 1 firstD).map Child.paid=[1,1] := by decide
example : (thirdChildren thirdS 0 1 thirdD).map Child.paid=[1,1] := by decide
example : (pendantChild firstS 0 1).sourceForest=[] := by decide
example : siblingEndpoint? (tiny true false true) [true,false,false]=some 1 := by decide
end Universal233.Rule5SourceOrientation.FalseControls
