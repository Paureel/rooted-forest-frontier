import ProbePrecontrols
open Universal233.RankConsumer.Controls Universal233.CoreProgram Universal233.RankDichotomy
example : (generate crossed two (inputRank crossed two-1)).outputs.isEmpty = false := by decide
example : (generate contiguous two (inputRank contiguous two-1)).outputs.isEmpty = true := by decide
example : (generate repeated (fun _ => 0) 0).outputs.isEmpty = false := by decide
