import GraphControls
open PureBridge BridgeReview
-- A shortest vertex of a disconnected support is not necessarily an ancestor.
example : ([false] : Address).IsPrefix [true] := by decide
