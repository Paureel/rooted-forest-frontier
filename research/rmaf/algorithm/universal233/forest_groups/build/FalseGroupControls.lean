import GroupControls
open RMAF ForestState ForestGroups.Controls
example : agrees (some ordinary) [cross1,cross2] [[0,2],[1,3]] = true := by decide
example : agrees (some bT) [b1,b2] [[3,4,5,6]] = true := by decide
example : additionalCost sources (aF ++ bF ++ cF) = 2 := by decide
