import GroupPriority
import Lean
open RMAF Lean
def treeJSON : Tree → Json
 | .leaf x => toJson x
 | .node a b => Json.arr #[treeJSON a,treeJSON b]
def optJSON (t : Option Tree) : Json := match t with | none => Json.null | some s => treeJSON s
def ratJSON (r : Rat) : Json := Json.mkObj [("num",toJson r.num),("den",toJson r.den)]
open ForestState ForestGroups RestrictionBridge
 def ownsBool (ss : List Tree) (Q : List (List Nat)) : Bool := ss.all (fun s => Q.any (contained (leaves s)))
 def crossBool (T : Option Tree) (ss : List Tree) (Q : List (List Nat)) : Bool := match T with
 | none => true
 | some t => Q.all (fun U => Q.all (fun V => if U=V then true else
    (owned ss U).all (fun s => (owned ss V).all (fun r => disjointVertices (minimalVertices (leaves s) t) (minimalVertices (leaves r) t)))))
 def groupJSON (T : Option Tree) (ss : List Tree) (Q F : List (List Nat)) : Json := Json.mkObj [
 ("proper",toJson (proper T ss)),("checked_Q",toJson (partitionCheck (labels T) Q)),("ownership",toJson (ownsBool ss Q)),
 ("cross",toJson (crossBool T ss Q)),("global_agrees",toJson (agrees T ss F)),("additional",toJson (additionalCost ss F)),
 ("whole_group_disjoint",toJson (targetEmbeddings T Q)),
 ("within",toJson (match T with | none => false | some t => Q.any (fun U => !(pairwiseEmbeddings t ((owned ss U).map leaves))))),
 ("local",toJson (Q.map (fun U => Json.mkObj [("target",optJSON (localTarget T U)),("sources",toJson ((owned ss U).map treeJSON)),
   ("indices",toJson (((ss.zipIdx).filter (fun si => contained (leaves si.1) U)).map Prod.snd)),
   ("forest",toJson (family U F)),("agrees",toJson (agrees (localTarget T U) (owned ss U) (family U F))),
   ("cost",toJson (additionalCost (owned ss U) (family U F)))])))]
#eval IO.println ("CASE:root-overlapping-B|" ++ (groupJSON (some (Tree.node (Tree.node (Tree.node (Tree.node (Tree.leaf 0) (Tree.leaf 1)) (Tree.leaf 2)) (Tree.node (Tree.node (Tree.leaf 3) (Tree.leaf 4)) (Tree.node (Tree.leaf 5) (Tree.leaf 6)))) (Tree.leaf 7))) [(Tree.node (Tree.leaf 0) (Tree.node (Tree.leaf 1) (Tree.leaf 2))), (Tree.node (Tree.leaf 3) (Tree.leaf 5)), (Tree.node (Tree.leaf 4) (Tree.leaf 6)), (Tree.leaf 7)] [[0, 1, 2], [3, 4, 5, 6], [7]] [[0, 1], [2], [3], [4], [5], [6], [7]]).compress)
#eval IO.println ("CASE:root-cheaper-B-valid|" ++ (groupJSON (some (Tree.node (Tree.node (Tree.node (Tree.node (Tree.leaf 0) (Tree.leaf 1)) (Tree.leaf 2)) (Tree.node (Tree.node (Tree.leaf 3) (Tree.leaf 4)) (Tree.node (Tree.leaf 5) (Tree.leaf 6)))) (Tree.leaf 7))) [(Tree.node (Tree.leaf 0) (Tree.node (Tree.leaf 1) (Tree.leaf 2))), (Tree.node (Tree.leaf 3) (Tree.leaf 5)), (Tree.node (Tree.leaf 4) (Tree.leaf 6)), (Tree.leaf 7)] [[0, 1, 2], [3, 4, 5, 6], [7]] [[0, 1], [2], [3], [5], [4, 6], [7]]).compress)
#eval IO.println ("CASE:reordered-groups-sources-blocks|" ++ (groupJSON (some (Tree.node (Tree.node (Tree.node (Tree.node (Tree.leaf 0) (Tree.leaf 1)) (Tree.leaf 2)) (Tree.node (Tree.node (Tree.leaf 3) (Tree.leaf 4)) (Tree.node (Tree.leaf 5) (Tree.leaf 6)))) (Tree.leaf 7))) [(Tree.node (Tree.leaf 4) (Tree.leaf 6)), (Tree.leaf 7), (Tree.node (Tree.leaf 0) (Tree.node (Tree.leaf 1) (Tree.leaf 2))), (Tree.node (Tree.leaf 3) (Tree.leaf 5))] [[7], [3, 4, 5, 6], [0, 1, 2]] [[7], [6], [4], [2], [0, 1], [5], [3]]).compress)
#eval IO.println ("CASE:C-absent|" ++ (groupJSON (some (Tree.node (Tree.node (Tree.node (Tree.leaf 0) (Tree.leaf 1)) (Tree.leaf 2)) (Tree.node (Tree.node (Tree.leaf 3) (Tree.leaf 4)) (Tree.node (Tree.leaf 5) (Tree.leaf 6))))) [(Tree.node (Tree.leaf 0) (Tree.node (Tree.leaf 1) (Tree.leaf 2))), (Tree.node (Tree.leaf 3) (Tree.leaf 5)), (Tree.node (Tree.leaf 4) (Tree.leaf 6))] [[0, 1, 2], [3, 4, 5, 6]] [[0, 1], [2], [3], [4], [5], [6]]).compress)
#eval IO.println ("CASE:none-empty|" ++ (groupJSON none [] [] []).compress)
#eval IO.println ("CASE:singleton|" ++ (groupJSON (some (Tree.leaf 7)) [(Tree.leaf 7)] [[7]] [[7]]).compress)
#eval IO.println ("CASE:whole-group-hulls-overlap-only|" ++ (groupJSON (some (Tree.node (Tree.node (Tree.leaf 0) (Tree.leaf 1)) (Tree.node (Tree.leaf 2) (Tree.leaf 3)))) [(Tree.leaf 0), (Tree.leaf 1), (Tree.leaf 2), (Tree.leaf 3)] [[0, 2], [1, 3]] [[0], [1], [2], [3]]).compress)
#eval IO.println ("CASE:cross-group-overlap-bad-concat|" ++ (groupJSON (some (Tree.node (Tree.node (Tree.leaf 0) (Tree.leaf 1)) (Tree.node (Tree.leaf 2) (Tree.leaf 3)))) [(Tree.node (Tree.leaf 0) (Tree.leaf 2)), (Tree.node (Tree.leaf 1) (Tree.leaf 3))] [[0, 2], [1, 3]] [[0, 2], [1, 3]]).compress)
#eval IO.println ("CASE:cross-group-overlap-refined-valid|" ++ (groupJSON (some (Tree.node (Tree.node (Tree.leaf 0) (Tree.leaf 1)) (Tree.node (Tree.leaf 2) (Tree.leaf 3)))) [(Tree.node (Tree.leaf 0) (Tree.leaf 2)), (Tree.node (Tree.leaf 1) (Tree.leaf 3))] [[0, 2], [1, 3]] [[0], [1], [2], [3]]).compress)
#eval IO.println ("CASE:missing-whole-source-ownership|" ++ (groupJSON (some (Tree.node (Tree.node (Tree.leaf 0) (Tree.leaf 1)) (Tree.node (Tree.leaf 2) (Tree.leaf 3)))) [(Tree.node (Tree.leaf 0) (Tree.leaf 2)), (Tree.leaf 1), (Tree.leaf 3)] [[0, 1], [2, 3]] [[0], [1], [2], [3]]).compress)
#eval IO.println ("CASE:none-nonempty-source|" ++ (groupJSON none [(Tree.leaf 7)] [] []).compress)
