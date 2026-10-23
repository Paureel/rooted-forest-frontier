import ExpansionPartitionV2
open RMAF ForestState
example :
 let T := Tree.node (.node (.leaf 0) (.leaf 1)) (.node (.leaf 0) (.leaf 1))
 (leaves (contract 0 1 3 T)).length+1=(leaves T).length := by decide
