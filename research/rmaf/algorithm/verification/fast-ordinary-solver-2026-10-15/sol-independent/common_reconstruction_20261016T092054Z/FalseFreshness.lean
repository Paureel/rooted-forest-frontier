import ExpansionPartitionV2
open RMAF ForestState
example : (leaves (contract 0 1 2 (.node (.node (.leaf 0) (.leaf 1)) (.leaf 2)))).Nodup := by decide
