import GuardControls
namespace Universal233.OrdinaryPriorityBridge.FalseControls
open RMAF CoreGraph Integration VertexGeometry CutRealization HardParent CherryBranching Rule5Local Rule5Local.Pre Rule5Classification Rule5Classification.Controls Rule5FinalClassification Rule5FinalClassification.Controls OrdinaryPriorityBridge.Controls
set_option maxRecDepth 10000
example : CherryBranching.select commonT commonS=some (.one,commonC) := by decide
example : CherryBranching.select commonT commonS=some (.hard2,{commonC with a:=4,b:=3}) := by decide
example : Rule5Local.rule4 Rule4.Controls.T Rule4.Controls.S=false := by decide
example : (Rule4.select Rule4.Controls.T (Rule4.Controls.swap01 Rule4.Controls.S)).isSome=false := by decide
example : pairwiseEmbeddings commonT (pendantPartition commonS commonC.a commonC.b)=true := by decide
example : admitted commonT commonS commonC.a commonC.b=true := by decide
end Universal233.OrdinaryPriorityBridge.FalseControls
