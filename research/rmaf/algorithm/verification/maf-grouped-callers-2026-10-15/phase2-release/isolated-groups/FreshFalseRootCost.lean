import FreshConsumer
open RMAF ForestState ForestGroups
example : additionalCost [(Tree.node (Tree.leaf 0) (Tree.node (Tree.leaf 1) (Tree.leaf 2))), (Tree.node (Tree.leaf 3) (Tree.leaf 5)), (Tree.node (Tree.leaf 4) (Tree.leaf 6)), (Tree.leaf 7)] [[0, 1], [2], [3], [4], [5], [6], [7]]=2 := by decide
