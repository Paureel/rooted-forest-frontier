import GraphRouteControls
open RMAF DegreeTwoGraphControls
example : ¬ (minimalVertices [0] pathT = minimalVertices [0] pathU) := by decide
