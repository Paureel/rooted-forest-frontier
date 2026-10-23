import PairPrecontrols
open Universal233.CoreProgram Universal233.PairAssembly.Controls Universal233.SourceCoverage RMAF
example : ((generate s color 6).outputs.any (fun o => o.sourceCuts.length == 3)) = true := by decide
example : (dedupNat ((leaves s).map color)).length = 3 := by decide
example : ((generate s color 6).outputs.any (fun o => refinesBool originalF o.partition)) = true := by decide
