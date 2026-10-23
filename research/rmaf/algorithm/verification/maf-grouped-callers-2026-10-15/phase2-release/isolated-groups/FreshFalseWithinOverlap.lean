import FreshConsumer
open RMAF ForestState ForestGroups
example : disjointVertices (minimalVertices [3,5] NonauthorGroupedConsumer.T) (minimalVertices [4,6] NonauthorGroupedConsumer.T)=true := by decide
