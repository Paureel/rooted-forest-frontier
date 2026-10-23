import RMAF
example : [false, false] ∉ RMAF.minimalVertices [1,2] (.node (.node (.leaf 1) (.leaf 2)) (.node (.leaf 3) (.leaf 4))) := by decide
