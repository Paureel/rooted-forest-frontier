import LocalWorkControls
open Universal233.Rule5LocalWork RMAF OrdinaryCommonSplit.Source
example : labelMax [0,3]+2≤labelMax [0,3] := by decide
example : (mergeMeter [0] [2] 0 2 4 5 [[0],[0]] [[2],[2]]).value.length≤3 := by decide
example : cells [List.replicate 10 0]≤2*(leaves (.leaf 0)).length := by decide
example : (bestMeter falseCheck [[],[[0]],[]]).work=1 := by decide
