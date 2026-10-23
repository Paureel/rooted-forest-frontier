import OutputControls
open RMAF ForestState OutputState OutputState.Controls
example : pairwiseEmbeddings ordinary Q = true := by decide
example : agreement crossed ordinary Q = true := by decide
example : (sourceForest crossed Q).length = 1 := by decide
example : additionalCost (sourceForest crossed Q) F = 3 := by decide
