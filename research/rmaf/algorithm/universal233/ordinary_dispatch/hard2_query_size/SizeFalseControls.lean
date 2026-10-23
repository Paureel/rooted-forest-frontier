import SizeControls
open RMAF ForestState ForestGroups OrdinaryDispatch.Hard2Size.Controls
example : (labels (some (.node (.leaf 0) (.leaf 1)))).length≤(leaves (.leaf 0)).length := by decide
example : (labels (localTarget (some target) [0,3])).length=3 := by decide
example : (localTarget (some target) [9]).isSome=true := by decide
example : (3 : Nat)+2*4+2≤3+2*4 := by decide
