import ActualCommonLiftV4
open RMAF
example : agreement (.node (.node (.leaf 0) (.leaf 1)) (.leaf 2))
 (.node (.leaf 2) (.node (.leaf 1) (.leaf 0))) [[0],[2]]=true := by decide
