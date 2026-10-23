import RMAF
example : RMAF.minimalVertices [1,2] (.node (.node (.leaf 1) (.leaf 2)) (.node (.leaf 3) (.leaf 4))) = [[false], [false,false], [false,true]] := by exact True.intro
