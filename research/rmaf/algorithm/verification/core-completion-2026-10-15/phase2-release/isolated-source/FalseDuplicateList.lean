import CoreProgram
open Universal233.CoreProgram
example : (combine (generate Controls.crossed Controls.parity 3) (generate Controls.crossed Controls.parity 3)).outputs.length = 2 := by decide
