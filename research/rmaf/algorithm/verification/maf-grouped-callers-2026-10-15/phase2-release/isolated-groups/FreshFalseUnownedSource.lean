import FreshConsumer
open RMAF ForestState ForestGroups
example : ownsBool [(Tree.node (Tree.leaf 0) (Tree.leaf 2)), (Tree.leaf 1), (Tree.leaf 3)] [[0, 1], [2, 3]]=true := by decide
