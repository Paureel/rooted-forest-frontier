import FreshConsumer
open RMAF ForestState ForestGroups
example : crossBool (some (Tree.node (Tree.node (Tree.leaf 0) (Tree.leaf 1)) (Tree.node (Tree.leaf 2) (Tree.leaf 3)))) [(Tree.leaf 0), (Tree.leaf 1), (Tree.leaf 2), (Tree.leaf 3)] [[0, 2], [1, 3]]=false := by decide
