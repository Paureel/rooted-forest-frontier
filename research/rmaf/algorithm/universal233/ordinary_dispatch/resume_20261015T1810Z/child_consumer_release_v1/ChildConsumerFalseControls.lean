import ChildConsumerControls
open RMAF OrdinaryDispatch OrdinaryDispatch.Controls Universal233.CherryBranching
example : runChildren noOrdinary T S 1 [singletonChild S 0] = some [[0],[2],[1,3]] := by cbv
example : runChildren noOrdinary T S 2 [] = some [[0],[2],[1,3]] := by cbv
