import CoreProgram
open Universal233.CoreProgram Universal233.CoreProgram.Controls
/-- Deliberately false: deleting one branch still yields both extremal cores. -/
example : parts { (generate crossed parity 3) with
    outputs := (generate crossed parity 3).outputs.take 1 } =
    [[[0], [1, 3], [2]], [[0, 2], [1], [3]]] := by decide
