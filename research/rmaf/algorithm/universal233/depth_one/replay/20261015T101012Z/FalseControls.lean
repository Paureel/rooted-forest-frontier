import Controls
open RMAF Universal233.DepthOne Universal233.DepthOne.Controls
example : pretest01 RMAF.Controls.leftTree crossed = .found none := by decide
example : cutCost (some [false]) = 0 := by decide
example : ([] : Vertex) ∈ edges crossed := by decide
example : forest RMAF.Controls.rightTree (some [false,true,true]) = [[2],[0,1,2,3]] := by decide
