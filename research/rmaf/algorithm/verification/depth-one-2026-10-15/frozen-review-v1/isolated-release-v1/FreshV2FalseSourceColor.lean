import SourceColorControls
open RMAF Universal233.DepthOne Universal233.CoreProgram
example : (generate Controls.crossed (twoColor [0,1]) 1).outputs.length = 1 := by decide
