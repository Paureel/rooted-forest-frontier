import GraphControls
open PureBridge BridgeReview
-- Same unfold/decide tactic as the clean true-edge twin.
example : Adj [] [false,false] := by
  unfold Adj
  decide
