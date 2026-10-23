import ActualCommonLift
open RMAF
example : let T := Tree.node (.node (.leaf 0) (.leaf 1)) (.node (.leaf 2) (.leaf 3))
 agreement T T [[0,2],[1,3]]=true := by decide
