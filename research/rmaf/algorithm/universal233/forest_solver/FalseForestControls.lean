import ForestPrecontrols
open GenericForest GenericForest.Controls RMAF ForestState OutputState
-- Explicit paid cost is not an intrinsic minimum discount.
example : additionalCost [a] [leaves a] ≥ 1 := by decide
-- Label partition alone does not supply the original source embeddings.
example : agrees (some (cross 0)) (sourceForest (four 0) [[0,2],[1,3]]) [[0,2],[1,3]] = true →
    agrees (some (cross 0)) [four 0] [[0,2],[1,3]] = true := by decide
