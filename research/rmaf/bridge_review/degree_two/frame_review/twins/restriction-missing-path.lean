import Controls
open RMAF RestrictionRouteControls
example : ¬ (minimalVertices [0,2] tPath = [[],[false,false],[true]]) := by decide
