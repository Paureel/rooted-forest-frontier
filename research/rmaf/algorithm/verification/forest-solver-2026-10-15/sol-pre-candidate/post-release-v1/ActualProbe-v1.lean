import ForestResource
import Lean
open Lean RMAF ForestState GenericForest
open Universal233.CoreProgram Universal233.PaidQueries

def mockTable : List (Tree × Tree × Nat × Forest) := [
(.leaf 0,.leaf 0,0,[[0]]),
(.leaf 1,.leaf 1,0,[[1]]),
((.node (.leaf 0) (.leaf 1)),(.node (.leaf 0) (.leaf 1)),0,[[0,1]]),
(.leaf 2,.leaf 2,0,[[2]]),
(.leaf 3,.leaf 3,0,[[3]]),
((.node (.leaf 2) (.leaf 3)),(.node (.leaf 2) (.leaf 3)),0,[[2,3]]),
((.node (.leaf 0) (.leaf 2)),(.node (.leaf 0) (.leaf 2)),0,[[0,2]]),
((.node (.leaf 0) (.leaf 3)),(.node (.leaf 0) (.leaf 3)),0,[[0,3]]),
((.node (.leaf 2) (.leaf 1)),(.node (.leaf 1) (.leaf 2)),0,[[1,2]]),
((.node (.leaf 1) (.leaf 3)),(.node (.leaf 1) (.leaf 3)),0,[[1,3]]),
((.node ((.node (.leaf 0) (.leaf 2))) (.leaf 1)),(.node ((.node (.leaf 0) (.leaf 1))) (.leaf 2)),1,[[0,1],[2]]),
((.node (.leaf 0) ((.node (.leaf 1) (.leaf 3)))),(.node ((.node (.leaf 0) (.leaf 1))) (.leaf 3)),1,[[0,1],[3]]),
((.node ((.node (.leaf 0) (.leaf 2))) (.leaf 3)),(.node (.leaf 0) ((.node (.leaf 2) (.leaf 3)))),1,[[0,2],[3]]),
((.node (.leaf 2) ((.node (.leaf 1) (.leaf 3)))),(.node (.leaf 1) ((.node (.leaf 2) (.leaf 3)))),1,[[1,2],[3]]),
((.node ((.node (.leaf 0) (.leaf 2))) ((.node (.leaf 1) (.leaf 3)))),(.node ((.node (.leaf 0) (.leaf 1))) ((.node (.leaf 2) (.leaf 3)))),2,[[0,1],[2],[3]]),
(.leaf 4,.leaf 4,0,[[4]]),
((.node (.leaf 0) (.leaf 4)),(.node (.leaf 0) (.leaf 4)),0,[[0,4]]),
((.node (.leaf 1) (.leaf 4)),(.node (.leaf 1) (.leaf 4)),0,[[1,4]]),
((.node ((.node (.leaf 0) (.leaf 1))) (.leaf 4)),(.node ((.node (.leaf 0) (.leaf 1))) (.leaf 4)),0,[[0,1,4]]),
(.leaf 5,.leaf 5,0,[[5]]),
((.node (.leaf 2) (.leaf 5)),(.node (.leaf 2) (.leaf 5)),0,[[2,5]]),
((.node (.leaf 3) (.leaf 5)),(.node (.leaf 3) (.leaf 5)),0,[[3,5]]),
((.node ((.node (.leaf 2) (.leaf 3))) (.leaf 5)),(.node ((.node (.leaf 2) (.leaf 3))) (.leaf 5)),0,[[2,3,5]]),
(.leaf 37,.leaf 37,0,[[37]]),
(.leaf 11,.leaf 11,0,[[11]]),
(.leaf 103,.leaf 103,0,[[103]]),
((.node (.leaf 11) (.leaf 37)),(.node (.leaf 11) (.leaf 37)),0,[[11,37]]),
((.node (.leaf 11) (.leaf 103)),(.node (.leaf 11) (.leaf 103)),0,[[11,103]]),
((.node (.leaf 37) (.leaf 103)),(.node (.leaf 37) (.leaf 103)),0,[[37,103]]),
((.node (.leaf 11) ((.node (.leaf 37) (.leaf 103)))),(.node (.leaf 11) ((.node (.leaf 37) (.leaf 103)))),0,[[11,37,103]]),
(.leaf 48,.leaf 48,0,[[48]]),
((.node (.leaf 48) (.leaf 11)),(.node (.leaf 48) (.leaf 11)),0,[[11,48]]),
(.leaf 122,.leaf 122,0,[[122]]),
(.leaf 85,.leaf 85,0,[[85]]),
((.node (.leaf 122) (.leaf 85)),(.node (.leaf 122) (.leaf 85)),0,[[85,122]]),
((.node (.leaf 122) (.leaf 48)),(.node (.leaf 122) (.leaf 48)),0,[[48,122]]),
((.node (.leaf 122) (.leaf 11)),(.node (.leaf 122) (.leaf 11)),0,[[11,122]]),
((.node (.leaf 48) (.leaf 85)),(.node (.leaf 85) (.leaf 48)),0,[[48,85]]),
((.node (.leaf 85) (.leaf 11)),(.node (.leaf 85) (.leaf 11)),0,[[11,85]]),
((.node ((.node (.leaf 122) (.leaf 48))) (.leaf 85)),(.node ((.node (.leaf 122) (.leaf 85))) (.leaf 48)),1,[[48,85],[122]]),
((.node (.leaf 122) ((.node (.leaf 85) (.leaf 11)))),(.node ((.node (.leaf 122) (.leaf 85))) (.leaf 11)),1,[[11,85],[122]]),
((.node ((.node (.leaf 122) (.leaf 48))) (.leaf 11)),(.node (.leaf 122) ((.node (.leaf 48) (.leaf 11)))),1,[[11,48],[122]]),
((.node (.leaf 48) ((.node (.leaf 85) (.leaf 11)))),(.node (.leaf 85) ((.node (.leaf 48) (.leaf 11)))),1,[[11,48],[85]]),
((.node ((.node (.leaf 122) (.leaf 48))) ((.node (.leaf 85) (.leaf 11)))),(.node ((.node (.leaf 122) (.leaf 85))) ((.node (.leaf 48) (.leaf 11)))),2,[[11,48],[85],[122]]),
(.leaf 159,.leaf 159,0,[[159]]),
((.node (.leaf 159) (.leaf 48)),(.node (.leaf 159) (.leaf 48)),0,[[48,159]]),
((.node (.leaf 159) (.leaf 11)),(.node (.leaf 159) (.leaf 11)),0,[[11,159]]),
((.node (.leaf 159) ((.node (.leaf 48) (.leaf 11)))),(.node (.leaf 159) ((.node (.leaf 48) (.leaf 11)))),0,[[11,48,159]]),
(.leaf 196,.leaf 196,0,[[196]]),
((.node (.leaf 196) (.leaf 122)),(.node (.leaf 196) (.leaf 122)),0,[[122,196]]),
((.node (.leaf 196) (.leaf 85)),(.node (.leaf 196) (.leaf 85)),0,[[85,196]]),
((.node (.leaf 196) ((.node (.leaf 122) (.leaf 85)))),(.node (.leaf 196) ((.node (.leaf 122) (.leaf 85)))),0,[[85,122,196]])
]

def mockOrdinary (t s : Tree) (q : Nat) : Option Forest :=
  (mockTable.find? fun r => sameShape t r.1 && sameShape s r.2.1).bind fun r =>
    if r.2.2.1 ≤ q then some r.2.2.2 else none

def treeJson : Tree → Json
  | .leaf x => toJson x
  | .node a b => Json.arr #[treeJson a,treeJson b]
def targetJson : Option Tree → Json
  | none => Json.null
  | some t => treeJson t
def sourcesJson (ss : List Tree) : Json := Json.arr (ss.toArray.map treeJson)
def vertexJson (v : Vertex) : Json := toJson (v.map fun b => if b then (1:Nat) else 0)
def outputJson (i : Nat) (o : Output) (ss : List Tree) (q : Nat) : Json := Json.mkObj [
  ("parent",toJson i),("partition",toJson o.partition),
  ("sourceCuts",Json.arr (o.sourceCuts.toArray.map vertexJson)),
  ("d",toJson o.sourceCuts.length),("paid_guard",toJson (decide (1 ≤ o.sourceCuts.length ∧ o.sourceCuts.length ≤ q))),
  ("child_sources",sourcesJson (replace ss i o.partition))]
def generationJson (t s : Tree) (v : Vertex) (q : Nat) : Json :=
  let r := generate s (colorLabel t v) q
  Json.mkObj [("visited",toJson r.visited),("childAttempts",toJson r.childAttempts),
    ("pruned",toJson r.pruned),("refusals",toJson r.refusals),
    ("colors",toJson ((leaves s).map fun x => (x,colorLabel t v x)))]
def jobJson : Job (Tree × Tree) Forest → Json
  | .hard p => Json.mkObj [("kind",toJson "hard"),("target",treeJson p.1),("source",treeJson p.2)]
  | .resolved p c a => Json.mkObj [("kind",toJson "resolved"),("target",treeJson p.1),
      ("source",treeJson p.2),("cost",toJson c),("forest",toJson a)]

def trace (T : Option Tree) (ss : List Tree) (q : Nat) : List Json :=
  let base := [("T",targetJson T),("ss",sourcesJson ss),("q",toJson q),
    ("actual_return",toJson (GenericForest.solve mockOrdinary T ss q)),
    ("proper",toJson (proper T ss)),("current_agrees",toJson (agrees T ss (ss.map leaves)))]
  if proper T ss then
    if agrees T ss (ss.map leaves) then [Json.mkObj (("case",toJson "done")::base)] else
    match T,ss with
    | none,_ => [Json.mkObj (("case",toJson "none")::base)]
    | some t,[s] => [Json.mkObj ([("case",toJson "singleton"),("query_target",treeJson t),
          ("query_source",treeJson s),("query_budget",toJson q),("ordinary_return",toJson (mockOrdinary t s q))]++base)]
    | some t,_ =>
      match overlap t ss with
      | none =>
        let detail := match jobs t ss with
          | none => [("jobs",Json.null)]
          | some js =>
            let r := meterSchedule (fun p b => (mockOrdinary p.1 p.2 b).map (fun F => (F.length-1,F)))
              (fun _ _ => 0) q js
            [("jobs",Json.arr (js.toArray.map jobJson)),("allocated",toJson (allocated q js)),
              ("knownCost",toJson (knownCost js)),("pending",toJson (pending js)),
              ("query_calls",Json.arr (r.queries.toArray.map fun (p,b) => Json.mkObj [
                ("target",treeJson p.1),("source",treeJson p.2),("budget",toJson b),
                ("answer",toJson (mockOrdinary p.1 p.2 b))])),
              ("meter_answers",toJson r.value.answers),("meter_calls",toJson r.value.calls),
              ("actual_attempt_answers",toJson ((disjointAttempt t ss mockOrdinary q).bind (·.answers))),
              ("meter_callerWork",toJson r.callerWork),("meter_recursiveWork",toJson r.recursiveWork)]
        [Json.mkObj ([("case",toJson "disjoint")]++detail++base)]
      | some h =>
        let raw := branches t ss h q
        let event := Json.mkObj ([("case",toJson "overlap"),("selected_left",toJson h.left),
          ("selected_right",toJson h.right),("selected_vertex",vertexJson h.vertex),
          ("raw",Json.arr (raw.toArray.map fun (i,o) => outputJson i o ss q)),
          ("left_generation",match ss[h.left]? with | none => Json.null | some s => generationJson t s h.vertex q),
          ("right_generation",match ss[h.right]? with | none => Json.null | some s => generationJson t s h.vertex q)]++base)
        event :: (raw.flatMap fun (i,o) =>
          let d := o.sourceCuts.length
          if _hd : 1 ≤ d ∧ d ≤ q then trace T (replace ss i o.partition) (q-d) else [])
  else [Json.mkObj (("case",toJson "improper")::base)]
termination_by q
decreasing_by omega

def cases : List (String × Option Tree × List Tree × List Nat) := [
("crossed",some ((.node ((.node (.leaf 0) (.leaf 2))) ((.node (.leaf 1) (.leaf 3))))),[((.node (.leaf 0) (.leaf 1))),((.node (.leaf 2) (.leaf 3)))],[0,1,2]),
("sole_hard",some ((.node ((.node ((.node (.leaf 0) (.leaf 2))) ((.node (.leaf 1) (.leaf 3))))) (.leaf 4))),[((.node ((.node (.leaf 0) (.leaf 1))) ((.node (.leaf 2) (.leaf 3))))),(.leaf 4)],[0,1,2,3]),
("three_region",some ((.node ((.node ((.node (.leaf 0) (.leaf 2))) ((.node (.leaf 1) (.leaf 3))))) ((.node (.leaf 4) (.leaf 5))))),[((.node ((.node (.leaf 0) (.leaf 1))) (.leaf 4))),((.node ((.node (.leaf 2) (.leaf 3))) (.leaf 5)))],[1,2,3]),
("empty",none,[],[0,1]),
("leaf",some (.leaf 37),[(.leaf 37)],[0,1]),
("identical",some ((.node (.leaf 11) ((.node (.leaf 37) (.leaf 103))))),[((.node (.leaf 11) ((.node (.leaf 37) (.leaf 103)))))],[0,1]),
("unequal",some ((.node (.leaf 11) (.leaf 37))),[((.node (.leaf 11) (.leaf 103)))],[0,1]),
("duplicate_target",some ((.node (.leaf 11) (.leaf 11))),[((.node (.leaf 11) (.leaf 11)))],[0,1]),
("duplicate_source",some ((.node (.leaf 11) (.leaf 37))),[((.node (.leaf 11) (.leaf 37))),(.leaf 37)],[0,1]),
("empty_source_nonempty",some (.leaf 11),[],[0,1]),
("nonempty_source_empty",none,[(.leaf 11)],[0,1]),
("crossed_large_0",some ((.node ((.node (.leaf 122) (.leaf 48))) ((.node (.leaf 85) (.leaf 11))))),[((.node (.leaf 48) (.leaf 11))),((.node (.leaf 122) (.leaf 85)))],[0,1,2]),
("crossed_large_1",some ((.node ((.node (.leaf 122) (.leaf 48))) ((.node (.leaf 85) (.leaf 11))))),[((.node (.leaf 122) (.leaf 85))),((.node (.leaf 48) (.leaf 11)))],[0,1,2]),
("sole_hard_large_0",some ((.node (.leaf 159) ((.node ((.node (.leaf 122) (.leaf 48))) ((.node (.leaf 85) (.leaf 11))))))),[((.node ((.node (.leaf 122) (.leaf 85))) ((.node (.leaf 48) (.leaf 11))))),(.leaf 159)],[0,1,2,3]),
("sole_hard_large_1",some ((.node (.leaf 159) ((.node ((.node (.leaf 122) (.leaf 48))) ((.node (.leaf 85) (.leaf 11))))))),[(.leaf 159),((.node ((.node (.leaf 122) (.leaf 85))) ((.node (.leaf 48) (.leaf 11)))))],[0,1,2,3]),
("three_region_large_0",some ((.node ((.node (.leaf 196) (.leaf 159))) ((.node ((.node (.leaf 122) (.leaf 48))) ((.node (.leaf 85) (.leaf 11))))))),[((.node (.leaf 159) ((.node (.leaf 48) (.leaf 11))))),((.node (.leaf 196) ((.node (.leaf 122) (.leaf 85)))))],[1,2,3]),
("three_region_large_1",some ((.node ((.node (.leaf 196) (.leaf 159))) ((.node ((.node (.leaf 122) (.leaf 48))) ((.node (.leaf 85) (.leaf 11))))))),[((.node (.leaf 196) ((.node (.leaf 122) (.leaf 85))))),((.node (.leaf 159) ((.node (.leaf 48) (.leaf 11)))))],[1,2,3]),
("one_source_hard",some ((.node ((.node (.leaf 0) (.leaf 2))) ((.node (.leaf 1) (.leaf 3))))),[((.node ((.node (.leaf 0) (.leaf 1))) ((.node (.leaf 2) (.leaf 3)))))],[1,2,3])
]

def main (args : List String) : IO UInt32 := do
  if args.length != 2 then return 2
  let cs := if args[0]! == "pilot" then cases.take 1 else cases
  let rows := cs.flatMap fun c => c.2.2.2.map fun q =>
    Json.mkObj [("id",toJson c.1),("budget",toJson q),("trace",toJson (trace c.2.1 c.2.2.1 q))]
  IO.FS.writeFile args[1]! ((Json.arr rows.toArray).pretty++"\n")
  IO.println s!"actual probe rows: {rows.length}"
  return 0
