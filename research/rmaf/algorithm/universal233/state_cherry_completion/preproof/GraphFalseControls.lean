import GraphControls
open RMAF ForestState

-- Dropping the b-not-in-C hypothesis makes the endpoint statement false.
example : disjointVertices (minimalVertices [31,17] RootCherry) (minimalVertices [31] RootCherry) = true := by decide
example : cherryReady (some LeftCherry) [RightCherry] 17 31 47 = true := by decide
example : proper (some (.node (.leaf 17) (.leaf 17))) [.node (.leaf 17) (.leaf 17)] = true := by decide
example : additionalCost [RootCherry,.node (.leaf 47) (.leaf 59)] [[17],[31],[47,59]] = 3 - 1 := by decide
