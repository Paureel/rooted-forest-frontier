import FreshConsumer
open RMAF ForestState ForestGroups
example : pairwiseEmbeddings (.node (.node (.leaf 0) (.leaf 1)) (.node (.leaf 2) (.leaf 3))) [[0,2],[1,3]]=true := by decide
