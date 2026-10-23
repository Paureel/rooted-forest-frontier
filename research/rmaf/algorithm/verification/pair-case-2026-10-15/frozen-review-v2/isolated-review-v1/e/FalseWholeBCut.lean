import Controls
open RMAF BinaryExchange BinaryExchange.Controls
example : disjointVertices (minimalVertices [3,4] S) (minimalVertices [5,6] S) = true := by decide
