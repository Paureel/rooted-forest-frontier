import ReviewScope
open RMAF Universal233.CoreProgram Universal233.RankConsumer
example : optimizedFourOutputs (.leaf 0) (fun _ => 0) 0 =
 (generate (.leaf 0) (fun _ => 0) 0).outputs := by decide
