import ExpansionPartitionV2
open RMAF ForestState IndependentCommon
example : leaves (contract 0 1 3 (.node (.node (.leaf 0) (.leaf 1)) (.leaf 2)))=[3,2] := rfl
example : leaves (contract 0 1 3 (.node (.leaf 2) (.node (.leaf 1) (.leaf 0))))=[2,3] := rfl
example : partitionCheck [0,1,2] ([[3],[2]].map (expandBlock 0 1 3))=true := by decide
example : ¬partitionCheck [0,1,2] [[0],[2]]=true := by decide
example :
 let T := Tree.node (.node (.leaf 0) (.leaf 1)) (.node (.leaf 0) (.leaf 1))
 (leaves (contract 0 1 3 T)).length+1≠(leaves T).length := duplicate_uniqueness_required
example : ¬(leaves (contract 0 1 2 (.node (.node (.leaf 0) (.leaf 1)) (.leaf 2)))).Nodup := fresh_name_required
