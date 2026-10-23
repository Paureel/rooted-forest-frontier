import GraphControls
open PureBridge BridgeReview
-- Same unfold/decide tactic as the planted false two-bit edge.
example : Adj [] [false] := by
  unfold Adj
  decide
