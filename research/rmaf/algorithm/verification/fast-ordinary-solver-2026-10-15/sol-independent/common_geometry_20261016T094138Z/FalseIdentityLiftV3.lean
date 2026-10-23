import ActualCommonLiftV3
open RMAF ForestState IndependentGeometry
example : let T := Tree.node (.node (.leaf 0) (.leaf 1)) (.leaf 2)
 let C := contract 0 1 3 T
 ∀v∈minimalVertices (shrinkBlock 0 1 3 [0]) C,v∈minimalVertices [0] T := by decide
