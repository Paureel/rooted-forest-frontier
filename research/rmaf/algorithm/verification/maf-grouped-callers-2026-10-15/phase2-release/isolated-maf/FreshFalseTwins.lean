import FreshConsumer
open RMAF Universal233 MafScheduler
theorem clean0 : calls T1 S1 callback1 3 [[0,1,2,3],[4,5,6,7]]=[] := by decide
theorem clean1 : ((solveDisjoint T0 S0 callback0 4 [[0,1,2,3],[4,5,6,7]]).getD []).length-1=5 := by decide
theorem clean2 : calls T7 S7 callback7 3 [[0,1,2],[3,4,5,6]]=[2] := by decide
theorem clean3 : calls T10 S10 callback10 2 [[0,1,2,3]]=[2] := by decide
theorem clean4 : (calls T0 S0 callback0 4 [[0,1,2,3],[4,5,6,7]]).length=2 := by decide
theorem clean5 : (calls T0 S0 callback0 4 [[0,1,2,3],[4,5,6,7]]).length=2 := by decide
theorem clean6 : calls T5 S5 callback5 4 [[0,1,2,3],[4,5,6,7]]=[2] := by decide
theorem clean7 : solveDisjoint T6 S6 callback6 5 [[0,1,2,3],[4,5,6,7]]=none := by decide
theorem clean8 : prepare T0 S0 [[0,1,99],[2,3,4,5,6,7]]=none := by decide
theorem clean9 : agreement T0 S0 [[0,1,2,3],[4,5,6,7]]=false := by decide
