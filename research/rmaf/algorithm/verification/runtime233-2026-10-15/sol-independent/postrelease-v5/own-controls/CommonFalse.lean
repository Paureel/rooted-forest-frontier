import CommonBranchWork
open RMAF OrdinaryDispatch.FullSourceWork
example : (contractMeter 0 1 7 (.node (.leaf 0) (.leaf 2))).work=24 := by decide +kernel
