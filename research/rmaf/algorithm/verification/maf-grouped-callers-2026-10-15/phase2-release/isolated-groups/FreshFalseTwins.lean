import FreshConsumer
open RMAF ForestState ForestGroups
theorem clean0 : additionalCost [(Tree.node (Tree.leaf 0) (Tree.node (Tree.leaf 1) (Tree.leaf 2))), (Tree.node (Tree.leaf 3) (Tree.leaf 5)), (Tree.node (Tree.leaf 4) (Tree.leaf 6)), (Tree.leaf 7)] [[0, 1], [2], [3], [4], [5], [6], [7]]=3 := by decide
theorem clean1 : disjointVertices (minimalVertices [3,5] NonauthorGroupedConsumer.T) (minimalVertices [4,6] NonauthorGroupedConsumer.T)=false := by decide
theorem clean2 : agrees (some (.node (.node (.leaf 3) (.leaf 4)) (.node (.leaf 5) (.leaf 6)))) [.node (.leaf 3) (.leaf 5),.node (.leaf 4) (.leaf 6)] [[3,4,5,6]]=false := by decide
theorem clean3 : crossBool (some (Tree.node (Tree.node (Tree.leaf 0) (Tree.leaf 1)) (Tree.node (Tree.leaf 2) (Tree.leaf 3)))) [(Tree.node (Tree.leaf 0) (Tree.leaf 2)), (Tree.leaf 1), (Tree.leaf 3)] [[0, 1], [2, 3]]=true := by decide
theorem clean4 : ownsBool [(Tree.node (Tree.leaf 0) (Tree.leaf 2)), (Tree.leaf 1), (Tree.leaf 3)] [[0, 1], [2, 3]]=false := by decide
theorem clean5 : crossBool (some (Tree.node (Tree.node (Tree.leaf 0) (Tree.leaf 1)) (Tree.node (Tree.leaf 2) (Tree.leaf 3)))) [(Tree.leaf 0), (Tree.leaf 1), (Tree.leaf 2), (Tree.leaf 3)] [[0, 2], [1, 3]]=true := by decide
theorem clean6 : pairwiseEmbeddings (.node (.node (.leaf 0) (.leaf 1)) (.node (.leaf 2) (.leaf 3))) [[0,2],[1,3]]=false := by decide
theorem clean7 : additionalCost [NonauthorGroupedConsumer.b1,NonauthorGroupedConsumer.b2] [[3],[5],[4,6]]=1 := by decide
theorem clean8 : proper none [Tree.leaf 7]=false := by decide
theorem clean9 : partitionCheck [0,1,2] [[0,1,2],[]]=false := by decide
