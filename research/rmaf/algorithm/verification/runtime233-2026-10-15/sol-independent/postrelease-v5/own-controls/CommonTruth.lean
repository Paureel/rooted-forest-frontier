import CommonBranchWork
open RMAF OrdinaryDispatch.FullSourceWork
example : (labelMaxMeter [2,8,1]).value=8 := by decide +kernel
example : (labelMaxMeter [2,8,1]).work=13 := by decide +kernel
example : (commonFreshMeter (.node (.leaf 2) (.leaf 8))).value=9 := by decide +kernel
example : (contractMeter 0 1 7 (.node (.leaf 0) (.leaf 1))).value=.leaf 7 := by decide +kernel
example : (contractMeter 0 1 7 (.node (.leaf 0) (.leaf 1))).work=24 := by decide +kernel
example : (contractMeter 0 1 7 (.node (.leaf 0) (.leaf 2))).work=28 := by decide +kernel
example : (expandBlockMeter 0 1 7 [7,2,7]).value=[0,1,2,0,1] := by decide +kernel
example : (expandBlockMeter 0 1 7 [7,2,7]).work=37 := by decide +kernel
