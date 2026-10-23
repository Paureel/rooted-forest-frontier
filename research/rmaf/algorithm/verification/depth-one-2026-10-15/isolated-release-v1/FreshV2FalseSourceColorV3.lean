import SourceColorControls
open RMAF
example : (Universal233.CoreProgram.generate Universal233.DepthOne.Controls.crossed
    (Universal233.DepthOne.twoColor [0,1]) 1).outputs.length = 1 := by decide
