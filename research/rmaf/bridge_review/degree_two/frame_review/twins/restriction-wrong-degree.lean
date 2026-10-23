import Controls
open RMAF RestrictionRouteControls
example : ¬ (degree (minimalVertices [0,1] tRoot) [] = 3) := by decide
