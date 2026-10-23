import FreshConsumer
open RMAF ForestState ForestGroups
example : agrees (some (.node (.node (.leaf 3) (.leaf 4)) (.node (.leaf 5) (.leaf 6)))) [.node (.leaf 3) (.leaf 5),.node (.leaf 4) (.leaf 6)] [[3,4,5,6]]=true := by decide
