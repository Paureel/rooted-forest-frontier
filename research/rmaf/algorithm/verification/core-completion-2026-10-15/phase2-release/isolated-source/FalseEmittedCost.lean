import CoreProgram
open Universal233.CoreProgram
example : (Controls.costs (generate Controls.crossed Controls.parity 3)).all (fun c => decide (3 ≤ c)) = true := by decide
