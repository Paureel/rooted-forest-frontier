import CompletionConsumers
import Consumers
import Lean
open Lean RMAF ForestState
namespace SolReadouts
def jTree : Tree → Json
  | .leaf x => toJson x
  | .node l r => Json.arr #[jTree l,jTree r]
def jOpt : Option Tree → Json
  | none => Json.null
  | some t => jTree t
def jTrees (ss : List Tree) : Json := Json.arr (ss.map jTree).toArray
-- Declared literal/case adapter: theorem chooses unique a-owner and swaps if singleton.
def reviewCoalesce (F : List (List Nat)) (a b : Nat) : List (List Nat) :=
  let A := (F.find? (fun B => B.contains a)).getD []
  let B := (F.find? (fun B => B.contains b)).getD []
  if A.contains b then F else
    if A == [a] then reassignedForest F B a else reassignedForest F A b
def t0 : Option Tree := (some (RMAF.Tree.node (RMAF.Tree.leaf 0) (RMAF.Tree.leaf 1)))
def s0 : List Tree := [(RMAF.Tree.node (RMAF.Tree.leaf 0) (RMAF.Tree.leaf 1))]
def p0 : List (List (List Nat)) := [[[0],[1]],[[0,1]]]
def g0_0 : List (List Nat) := reviewCoalesce [[0],[1]] 0 1
def g0_1 : List (List Nat) := reviewCoalesce [[0,1]] 0 1
def t1 : Option Tree := (some (RMAF.Tree.node (RMAF.Tree.node (RMAF.Tree.leaf 0) (RMAF.Tree.leaf 1)) (RMAF.Tree.leaf 2)))
def s1 : List Tree := [(RMAF.Tree.node (RMAF.Tree.leaf 0) (RMAF.Tree.leaf 1)),(RMAF.Tree.leaf 2)]
def p1 : List (List (List Nat)) := [[[0],[1],[2]],[[0,1],[2]],[[1],[0,2]],[[0],[1,2]],[[0,1,2]]]
def g1_0 : List (List Nat) := reviewCoalesce [[0],[1],[2]] 0 1
def g1_1 : List (List Nat) := reviewCoalesce [[0,1],[2]] 0 1
def t2 : Option Tree := (some (RMAF.Tree.node (RMAF.Tree.node (RMAF.Tree.leaf 0) (RMAF.Tree.leaf 1)) (RMAF.Tree.leaf 2)))
def s2 : List Tree := [(RMAF.Tree.leaf 2),(RMAF.Tree.node (RMAF.Tree.leaf 0) (RMAF.Tree.leaf 1))]
def p2 : List (List (List Nat)) := [[[0],[1],[2]],[[0,1],[2]],[[1],[0,2]],[[0],[1,2]],[[0,1,2]]]
def g2_0 : List (List Nat) := reviewCoalesce [[0],[1],[2]] 0 1
def g2_1 : List (List Nat) := reviewCoalesce [[0,1],[2]] 0 1
def t3 : Option Tree := (some (RMAF.Tree.leaf 0))
def s3 : List Tree := [(RMAF.Tree.leaf 0)]
def p3 : List (List (List Nat)) := [[[0]]]
#eval IO.println (Json.arr #[
Json.mkObj [("kind", Json.str "state"), ("id", Json.str "root"), ("proper", toJson (proper t0 s0)), ("ready", toJson (cherryReady t0 s0 0 1 2)), ("labels", toJson (labels t0)), ("validity", toJson (p0.map (agrees t0 s0))), ("validCosts", toJson ((p0.filter (agrees t0 s0)).map (additionalCost s0))), ("qTruth", toJson ([0,1,2,3,4,5,8,1000000000].map (fun q => p0.any (fun F => agrees t0 s0 F && decide (additionalCost s0 F ≤ q))))), ("contractT", jOpt (t0.map (contract 0 1 2))), ("contractSS", jTrees (s0.map (contract 0 1 2))), ("expandedT", jOpt ((t0.map (contract 0 1 2)).map (expand 0 1 2))), ("expandedSS", jTrees ((s0.map (contract 0 1 2)).map (expand 0 1 2)))],
Json.mkObj [("kind", Json.str "initial"), ("id", Json.str "root"), ("originalValidity", toJson (p0.map (agreement (RMAF.Tree.node (RMAF.Tree.leaf 0) (RMAF.Tree.leaf 1)) (RMAF.Tree.node (RMAF.Tree.leaf 0) (RMAF.Tree.leaf 1)))))],
Json.mkObj [("kind", Json.str "cherry-forward"), ("id", Json.str "root-0"), ("G", toJson g0_0), ("validG", toJson (agrees t0 s0 g0_0)), ("oldCost", toJson (additionalCost s0 [[0],[1]])), ("newCost", toJson (additionalCost s0 g0_0)), ("H", toJson (g0_0.map (contractBlock 0 1 2))), ("validH", toJson (agrees (t0.map (contract 0 1 2)) (s0.map (contract 0 1 2)) (g0_0.map (contractBlock 0 1 2)))), ("costH", toJson (additionalCost (s0.map (contract 0 1 2)) (g0_0.map (contractBlock 0 1 2))))],
Json.mkObj [("kind", Json.str "cherry-forward"), ("id", Json.str "root-1"), ("G", toJson g0_1), ("validG", toJson (agrees t0 s0 g0_1)), ("oldCost", toJson (additionalCost s0 [[0,1]])), ("newCost", toJson (additionalCost s0 g0_1)), ("H", toJson (g0_1.map (contractBlock 0 1 2))), ("validH", toJson (agrees (t0.map (contract 0 1 2)) (s0.map (contract 0 1 2)) (g0_1.map (contractBlock 0 1 2)))), ("costH", toJson (additionalCost (s0.map (contract 0 1 2)) (g0_1.map (contractBlock 0 1 2))))],
Json.mkObj [("kind", Json.str "cherry-reverse"), ("id", Json.str "root-0"), ("F", toJson ([[2]].map (expandBlock 0 1 2))), ("valid", toJson (agrees t0 s0 ([[2]].map (expandBlock 0 1 2)))), ("cost", toJson (additionalCost s0 ([[2]].map (expandBlock 0 1 2)))), ("contractBack", toJson (([[2]].map (expandBlock 0 1 2)).map (contractBlock 0 1 2)))],
Json.mkObj [("kind", Json.str "state"), ("id", Json.str "triple-singleton-last"), ("proper", toJson (proper t1 s1)), ("ready", toJson (cherryReady t1 s1 0 1 3)), ("labels", toJson (labels t1)), ("validity", toJson (p1.map (agrees t1 s1))), ("validCosts", toJson ((p1.filter (agrees t1 s1)).map (additionalCost s1))), ("qTruth", toJson ([0,1,2,3,4,5,8,1000000000].map (fun q => p1.any (fun F => agrees t1 s1 F && decide (additionalCost s1 F ≤ q))))), ("cleanupT", jOpt (cleanupTarget t1 2)), ("cleanupSS", jTrees (cleanupSources s1 2)), ("contractT", jOpt (t1.map (contract 0 1 3))), ("contractSS", jTrees (s1.map (contract 0 1 3))), ("expandedT", jOpt ((t1.map (contract 0 1 3)).map (expand 0 1 3))), ("expandedSS", jTrees ((s1.map (contract 0 1 3)).map (expand 0 1 3)))],
Json.mkObj [("kind", Json.str "singleton-forward"), ("id", Json.str "triple-singleton-last-0"), ("F", toJson (cleanupForest [[0],[1],[2]] 2)), ("valid", toJson (agrees (cleanupTarget t1 2) (cleanupSources s1 2) (cleanupForest [[0],[1],[2]] 2))), ("oldCost", toJson (additionalCost s1 [[0],[1],[2]])), ("newCost", toJson (additionalCost (cleanupSources s1 2) (cleanupForest [[0],[1],[2]] 2)))],
Json.mkObj [("kind", Json.str "singleton-forward"), ("id", Json.str "triple-singleton-last-1"), ("F", toJson (cleanupForest [[0,1],[2]] 2)), ("valid", toJson (agrees (cleanupTarget t1 2) (cleanupSources s1 2) (cleanupForest [[0,1],[2]] 2))), ("oldCost", toJson (additionalCost s1 [[0,1],[2]])), ("newCost", toJson (additionalCost (cleanupSources s1 2) (cleanupForest [[0,1],[2]] 2)))],
Json.mkObj [("kind", Json.str "singleton-reverse"), ("id", Json.str "triple-singleton-last-0"), ("F", toJson ([[2],[0],[1]] : List (List Nat))), ("valid", toJson (agrees t1 s1 [[2],[0],[1]])), ("cost", toJson (additionalCost s1 [[2],[0],[1]]))],
Json.mkObj [("kind", Json.str "singleton-reverse"), ("id", Json.str "triple-singleton-last-1"), ("F", toJson ([[2],[0,1]] : List (List Nat))), ("valid", toJson (agrees t1 s1 [[2],[0,1]])), ("cost", toJson (additionalCost s1 [[2],[0,1]]))],
Json.mkObj [("kind", Json.str "cherry-forward"), ("id", Json.str "triple-singleton-last-0"), ("G", toJson g1_0), ("validG", toJson (agrees t1 s1 g1_0)), ("oldCost", toJson (additionalCost s1 [[0],[1],[2]])), ("newCost", toJson (additionalCost s1 g1_0)), ("H", toJson (g1_0.map (contractBlock 0 1 3))), ("validH", toJson (agrees (t1.map (contract 0 1 3)) (s1.map (contract 0 1 3)) (g1_0.map (contractBlock 0 1 3)))), ("costH", toJson (additionalCost (s1.map (contract 0 1 3)) (g1_0.map (contractBlock 0 1 3))))],
Json.mkObj [("kind", Json.str "cherry-forward"), ("id", Json.str "triple-singleton-last-1"), ("G", toJson g1_1), ("validG", toJson (agrees t1 s1 g1_1)), ("oldCost", toJson (additionalCost s1 [[0,1],[2]])), ("newCost", toJson (additionalCost s1 g1_1)), ("H", toJson (g1_1.map (contractBlock 0 1 3))), ("validH", toJson (agrees (t1.map (contract 0 1 3)) (s1.map (contract 0 1 3)) (g1_1.map (contractBlock 0 1 3)))), ("costH", toJson (additionalCost (s1.map (contract 0 1 3)) (g1_1.map (contractBlock 0 1 3))))],
Json.mkObj [("kind", Json.str "cherry-reverse"), ("id", Json.str "triple-singleton-last-0"), ("F", toJson ([[3],[2]].map (expandBlock 0 1 3))), ("valid", toJson (agrees t1 s1 ([[3],[2]].map (expandBlock 0 1 3)))), ("cost", toJson (additionalCost s1 ([[3],[2]].map (expandBlock 0 1 3)))), ("contractBack", toJson (([[3],[2]].map (expandBlock 0 1 3)).map (contractBlock 0 1 3)))],
Json.mkObj [("kind", Json.str "state"), ("id", Json.str "triple-singleton-first"), ("proper", toJson (proper t2 s2)), ("ready", toJson (cherryReady t2 s2 0 1 3)), ("labels", toJson (labels t2)), ("validity", toJson (p2.map (agrees t2 s2))), ("validCosts", toJson ((p2.filter (agrees t2 s2)).map (additionalCost s2))), ("qTruth", toJson ([0,1,2,3,4,5,8,1000000000].map (fun q => p2.any (fun F => agrees t2 s2 F && decide (additionalCost s2 F ≤ q))))), ("cleanupT", jOpt (cleanupTarget t2 2)), ("cleanupSS", jTrees (cleanupSources s2 2)), ("contractT", jOpt (t2.map (contract 0 1 3))), ("contractSS", jTrees (s2.map (contract 0 1 3))), ("expandedT", jOpt ((t2.map (contract 0 1 3)).map (expand 0 1 3))), ("expandedSS", jTrees ((s2.map (contract 0 1 3)).map (expand 0 1 3)))],
Json.mkObj [("kind", Json.str "singleton-forward"), ("id", Json.str "triple-singleton-first-0"), ("F", toJson (cleanupForest [[0],[1],[2]] 2)), ("valid", toJson (agrees (cleanupTarget t2 2) (cleanupSources s2 2) (cleanupForest [[0],[1],[2]] 2))), ("oldCost", toJson (additionalCost s2 [[0],[1],[2]])), ("newCost", toJson (additionalCost (cleanupSources s2 2) (cleanupForest [[0],[1],[2]] 2)))],
Json.mkObj [("kind", Json.str "singleton-forward"), ("id", Json.str "triple-singleton-first-1"), ("F", toJson (cleanupForest [[0,1],[2]] 2)), ("valid", toJson (agrees (cleanupTarget t2 2) (cleanupSources s2 2) (cleanupForest [[0,1],[2]] 2))), ("oldCost", toJson (additionalCost s2 [[0,1],[2]])), ("newCost", toJson (additionalCost (cleanupSources s2 2) (cleanupForest [[0,1],[2]] 2)))],
Json.mkObj [("kind", Json.str "singleton-reverse"), ("id", Json.str "triple-singleton-first-0"), ("F", toJson ([[2],[0],[1]] : List (List Nat))), ("valid", toJson (agrees t2 s2 [[2],[0],[1]])), ("cost", toJson (additionalCost s2 [[2],[0],[1]]))],
Json.mkObj [("kind", Json.str "singleton-reverse"), ("id", Json.str "triple-singleton-first-1"), ("F", toJson ([[2],[0,1]] : List (List Nat))), ("valid", toJson (agrees t2 s2 [[2],[0,1]])), ("cost", toJson (additionalCost s2 [[2],[0,1]]))],
Json.mkObj [("kind", Json.str "cherry-forward"), ("id", Json.str "triple-singleton-first-0"), ("G", toJson g2_0), ("validG", toJson (agrees t2 s2 g2_0)), ("oldCost", toJson (additionalCost s2 [[0],[1],[2]])), ("newCost", toJson (additionalCost s2 g2_0)), ("H", toJson (g2_0.map (contractBlock 0 1 3))), ("validH", toJson (agrees (t2.map (contract 0 1 3)) (s2.map (contract 0 1 3)) (g2_0.map (contractBlock 0 1 3)))), ("costH", toJson (additionalCost (s2.map (contract 0 1 3)) (g2_0.map (contractBlock 0 1 3))))],
Json.mkObj [("kind", Json.str "cherry-forward"), ("id", Json.str "triple-singleton-first-1"), ("G", toJson g2_1), ("validG", toJson (agrees t2 s2 g2_1)), ("oldCost", toJson (additionalCost s2 [[0,1],[2]])), ("newCost", toJson (additionalCost s2 g2_1)), ("H", toJson (g2_1.map (contractBlock 0 1 3))), ("validH", toJson (agrees (t2.map (contract 0 1 3)) (s2.map (contract 0 1 3)) (g2_1.map (contractBlock 0 1 3)))), ("costH", toJson (additionalCost (s2.map (contract 0 1 3)) (g2_1.map (contractBlock 0 1 3))))],
Json.mkObj [("kind", Json.str "cherry-reverse"), ("id", Json.str "triple-singleton-first-0"), ("F", toJson ([[3],[2]].map (expandBlock 0 1 3))), ("valid", toJson (agrees t2 s2 ([[3],[2]].map (expandBlock 0 1 3)))), ("cost", toJson (additionalCost s2 ([[3],[2]].map (expandBlock 0 1 3)))), ("contractBack", toJson (([[3],[2]].map (expandBlock 0 1 3)).map (contractBlock 0 1 3)))],
Json.mkObj [("kind", Json.str "state"), ("id", Json.str "last"), ("proper", toJson (proper t3 s3)), ("ready", toJson (cherryReady t3 s3 0 1 2)), ("labels", toJson (labels t3)), ("validity", toJson (p3.map (agrees t3 s3))), ("validCosts", toJson ((p3.filter (agrees t3 s3)).map (additionalCost s3))), ("qTruth", toJson ([0,1,2,3,4,5,8,1000000000].map (fun q => p3.any (fun F => agrees t3 s3 F && decide (additionalCost s3 F ≤ q))))), ("cleanupT", jOpt (cleanupTarget t3 0)), ("cleanupSS", jTrees (cleanupSources s3 0))],
Json.mkObj [("kind", Json.str "initial"), ("id", Json.str "last"), ("originalValidity", toJson (p3.map (agreement (RMAF.Tree.leaf 0) (RMAF.Tree.leaf 0))))],
Json.mkObj [("kind", Json.str "singleton-forward"), ("id", Json.str "last-0"), ("F", toJson (cleanupForest [[0]] 0)), ("valid", toJson (agrees (cleanupTarget t3 0) (cleanupSources s3 0) (cleanupForest [[0]] 0))), ("oldCost", toJson (additionalCost s3 [[0]])), ("newCost", toJson (additionalCost (cleanupSources s3 0) (cleanupForest [[0]] 0)))],
Json.mkObj [("kind", Json.str "singleton-reverse"), ("id", Json.str "last-0"), ("F", toJson ([[0]] : List (List Nat))), ("valid", toJson (agrees t3 s3 [[0]])), ("cost", toJson (additionalCost s3 [[0]]))]
]).compress
end SolReadouts
