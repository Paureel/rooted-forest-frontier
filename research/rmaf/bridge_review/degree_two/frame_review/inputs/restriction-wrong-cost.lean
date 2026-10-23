import Controls
open RMAF RestrictionRouteControls
example : ([[0],[2],[1],[3]] : List (List Nat)).length = ([[0,2],[1],[3]] : List (List Nat)).length := by decide
