import CompletionControls
open RMAF CoreProgram Universal233.Assembly Universal233.Assembly.Controls
example : taggedColor [0] [1] (fun _ => 0) (fun _ => 0) (fun _ => 0) 0 =
    taggedColor [0] [1] (fun _ => 0) (fun _ => 0) (fun _ => 0) 1 := by decide
example : (Universal233.WholeSourceMass.cliqueOutputs cliqueS cliqueT ca cb v 0).isEmpty = false := by decide
example : (Universal233.WholeSourceMass.diagonalOutputs diagS diagT da db v w 5).map
    (fun o => o.sourceCuts.length) = [4,4] := by decide
example : ((generate Universal233.HardParent.source4 (fun _ => 0) 0).outputs.all
    (fun o => agreement Universal233.HardParent.target4 Universal233.HardParent.source4 o.partition)) = true := by decide
