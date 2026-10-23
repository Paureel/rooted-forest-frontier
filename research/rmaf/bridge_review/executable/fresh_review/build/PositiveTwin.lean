import RMAF
open RMAF
example : minimalVertices [0,2] (.node (.node (.leaf 0) (.leaf 1)) (.node (.leaf 2) (.leaf 3))) = [[],[false],[false,false],[true],[true,false]] := by decide
