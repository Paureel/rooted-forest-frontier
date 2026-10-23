import CoreProgram
open Universal233.CoreProgram Universal233.CoreProgram.Controls
/-- Deliberately false: coverage by refinement preserves every input partition exactly. -/
example : [[0], [1], [2]] ∈ parts (generate cherry3 homColor 2) := by decide
