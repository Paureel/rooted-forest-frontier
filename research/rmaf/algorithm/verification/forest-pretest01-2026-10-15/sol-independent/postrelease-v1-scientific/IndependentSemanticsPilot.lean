import ForestPretestWork
open Lean RMAF ForestState ForestPretest01
set_option maxRecDepth 100000
def encodeIndependentResult : Result → Json
  | .refused => Json.mkObj [("kind",toJson "refused")]
  | .rejected => Json.mkObj [("kind",toJson "rejected")]
  | .found F => Json.mkObj [("kind",toJson "found"),("forest",toJson F)]
def independentT0 : Option Tree := (some (.leaf 0))
def independentS0 : List Tree := [(.leaf 0)]
def independentP0 : List (List (List Nat)) := [[[0]],[[0]]]
#eval IO.println ("SEMANTIC " ++ (Json.mkObj [
  ("id",toJson "singleton:base"),
  ("proper",toJson (proper independentT0 independentS0)),
  ("result",encodeIndependentResult (pretest01 independentT0 independentS0)),
  ("candidates",toJson (candidates independentS0)),
  ("candidate_valid",toJson ((candidates independentS0).map (agrees independentT0 independentS0))),
  ("candidate_cost",toJson ((candidates independentS0).map (additionalCost independentS0))),
  ("partition_valid",toJson (independentP0.map (agrees independentT0 independentS0)))
]).compress)
def independentT1 : Option Tree := (some (.node (.node (.leaf 0) (.leaf 1)) (.node (.leaf 2) (.leaf 3))))
def independentS1 : List Tree := [(.node (.leaf 0) (.leaf 2)),(.node (.leaf 1) (.leaf 3))]
def independentP1 : List (List (List Nat)) := [[[0],[1],[2],[3]],[[0,1],[2],[3]],[[1],[0,2],[3]],[[1],[2],[0,3]],[[0],[1,2],[3]],[[0,1,2],[3]],[[1,2],[0,3]],[[0],[2],[1,3]],[[0,2],[1,3]],[[2],[0,1,3]],[[0],[1],[2,3]],[[0,1],[2,3]],[[1],[0,2,3]],[[0],[1,2,3]],[[0,1,2,3]],[[3],[2],[1],[0]],[[3],[2],[1,0]],[[3],[2,0],[1]],[[3,0],[2],[1]],[[3],[2,1],[0]],[[3],[2,1,0]],[[3,0],[2,1]],[[3,1],[2],[0]],[[3,1],[2,0]],[[3,1,0],[2]],[[3,2],[1],[0]],[[3,2],[1,0]],[[3,2,0],[1]],[[3,2,1],[0]],[[3,2,1,0]]]
#eval IO.println ("SEMANTIC " ++ (Json.mkObj [
  ("id",toJson "crossed_forest:base"),
  ("proper",toJson (proper independentT1 independentS1)),
  ("result",encodeIndependentResult (pretest01 independentT1 independentS1)),
  ("candidates",toJson (candidates independentS1)),
  ("candidate_valid",toJson ((candidates independentS1).map (agrees independentT1 independentS1))),
  ("candidate_cost",toJson ((candidates independentS1).map (additionalCost independentS1))),
  ("partition_valid",toJson (independentP1.map (agrees independentT1 independentS1)))
]).compress)
