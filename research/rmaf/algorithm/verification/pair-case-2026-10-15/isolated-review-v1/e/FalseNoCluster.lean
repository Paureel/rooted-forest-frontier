import Controls
open RMAF BinaryExchange BinaryExchange.Controls
example : disjointVertices (minimalVertices [1,3] balanced) (minimalVertices [2,4] balanced) = true := by decide
