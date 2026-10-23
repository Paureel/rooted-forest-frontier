import LeastnessControls
open RMAF LeastEmbedding LeastEmbedding.Controls
example : invalidAmbient.all (fun v => (vertices quartet).contains v) = true := by decide
