import Controls
open RMAF RestrictionRouteControls
example : disjointVertices (minimalVertices [0,2] tFour) (minimalVertices [1,3] tFour) = true := by decide
