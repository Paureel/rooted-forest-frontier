import GraphControls
open PureBridge BridgeReview
-- A planted two-bit edge incorrectly suppresses the intermediate graph vertex.
example : Adj [] [false,false] := by decide
