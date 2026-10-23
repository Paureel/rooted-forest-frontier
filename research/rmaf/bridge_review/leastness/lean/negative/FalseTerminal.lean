import LeastnessControls
open RMAF LeastEmbedding LeastEmbedding.Controls
example : (terminals [0,1] quartet).all (fun v => missingTerminal.contains v) = true := by decide
