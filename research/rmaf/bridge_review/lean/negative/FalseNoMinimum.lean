import GraphControls
open PureBridge BridgeReview
-- Known-false planted conclusion at the explicit upward-walk witness.
example : ([false] : Address).IsPrefix [] := by decide
