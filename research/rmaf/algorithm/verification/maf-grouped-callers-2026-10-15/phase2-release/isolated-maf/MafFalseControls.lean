import MafPrecontrols
open RMAF Universal233.MafScheduler Universal233.MafScheduler.Precontrols
example : solveDisjoint (.node (cross 0) (cross 4)) (.node (four 0) (four 4)) table 3 [group 0,group 4]=some (three 0++three 4) := by decide
example : calls (.node (four 0) (cross 4)) (.node (comb 0) (four 4)) table 3 [group 0,group 4]=[3] := by decide
example : pairwiseEmbeddings (four 0) [[0,2],[1,3]]=true := by decide
example : agreement (four 0) (cross 0) [[0,2],[1,3]]=true := by decide
