import CoreProgram
open RMAF Universal233.CoreProgram
/-- Deliberately false: the original root is reported as a paid source cut. -/
example : (generate (.leaf 7) id 0).outputs = [⟨[[7]], [[]]⟩] := by decide
