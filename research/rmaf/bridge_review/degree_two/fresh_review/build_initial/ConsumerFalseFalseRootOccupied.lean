import ConsumerControls
open RMAF DegreeTwo.ConsumerControls
example : refined.any (fun b => (minimalVertices b quartet).contains []) = true := by decide
