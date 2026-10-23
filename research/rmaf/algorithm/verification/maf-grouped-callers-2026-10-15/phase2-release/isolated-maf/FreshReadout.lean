import OriginalPaid
import Lean
open RMAF Lean
def treeJSON : Tree → Json
 | .leaf x => toJson x
 | .node a b => Json.arr #[treeJSON a,treeJSON b]
def optJSON (t : Option Tree) : Json := match t with | none => Json.null | some s => treeJSON s
def ratJSON (r : Rat) : Json := Json.mkObj [("num",toJson r.num),("den",toJson r.den)]
open Universal233 PaidQueries MafScheduler
def jobJSON : Job (List Nat) Forest → Json
 | .hard U => Json.mkObj [("kind",toJson "hard"),("problem",toJson U)]
 | .resolved U c F => Json.mkObj [("kind",toJson "resolved"),("problem",toJson U),("cost",toJson c),("forest",toJson F)]
def prepJSON (p : Option (List (Job (List Nat) Forest))) : Json :=
 match p with | none => Json.null | some js => toJson (js.map jobJSON)
def preJSON (t s : Tree) : Json := match DepthOne.pretest01 t s with
 | .refused => toJson "refused"
 | .rejected => toJson "rejected"
 | .found c => Json.mkObj [("cost",toJson (DepthOne.cutCost c)),("forest",toJson (DepthOne.forest s c))]
def callerJSON (T S : Tree) (Q : Forest) (q : Nat) (solve : Tree → Tree → Nat → Option Forest) : Json :=
 let prep := prepare T S Q
 let a := attempt T S solve q Q
 let met := prep.map (meterSchedule (recursive T S solve) (fun U b => 1000*U.length+b) q)
 Json.mkObj [("prepare",prepJSON prep),("pretests",toJson (Q.map (fun U => match restrict U T,restrict U S with | some t,some s => preJSON t s | _,_ => Json.null))),
  ("restrictions",toJson (Q.map (fun U => Json.arr #[optJSON (restrict U T),optJSON (restrict U S)]))),
  ("proper_blocks",toJson (Q.map (properBlock T S))),
  ("forest",toJson (solveDisjoint T S solve q Q)),("calls",toJson (calls T S solve q Q)),
  ("bad_parents",toJson (badParents T S Q)),
  ("mass2",ratJSON (actualQueryMass 2 q (calls T S solve q Q))),
  ("mass233",ratJSON (actualQueryMass (233/100) q (calls T S solve q Q))),
  ("meter_queries",toJson ((met.map (fun r => r.queries.map (fun p => Json.mkObj [("problem",toJson p.1),("budget",toJson p.2)]))).getD [])),
  ("recursive_charge",toJson ((met.map (·.recursiveWork)).getD 0)),
  ("meter_caller_work",toJson ((met.map (·.callerWork)).getD 0)),
  ("source_target_Q_guards",toJson [decide (leaves T).Nodup,decide (leaves S).Nodup,partitionCheck (leaves T) Q,partitionCheck (leaves S) Q,pairwiseEmbeddings T Q,pairwiseEmbeddings S Q])]
def T0 : Tree := (Tree.node (Tree.node (Tree.node (Tree.leaf 0) (Tree.leaf 2)) (Tree.node (Tree.leaf 1) (Tree.leaf 3))) (Tree.node (Tree.node (Tree.leaf 4) (Tree.leaf 6)) (Tree.node (Tree.leaf 5) (Tree.leaf 7))))
def S0 : Tree := (Tree.node (Tree.node (Tree.node (Tree.leaf 0) (Tree.leaf 1)) (Tree.node (Tree.leaf 2) (Tree.leaf 3))) (Tree.node (Tree.node (Tree.leaf 4) (Tree.leaf 5)) (Tree.node (Tree.leaf 6) (Tree.leaf 7))))
def callback0 (t s : Tree) (b : Nat) : Option Forest := if t = (Tree.node (Tree.node (Tree.leaf 0) (Tree.leaf 2)) (Tree.node (Tree.leaf 1) (Tree.leaf 3))) ∧ s = (Tree.node (Tree.node (Tree.leaf 0) (Tree.leaf 1)) (Tree.node (Tree.leaf 2) (Tree.leaf 3))) then (if ([[0, 1], [2], [3]] : Forest).length-1 ≤ b then some [[0, 1], [2], [3]] else none) else (if t = (Tree.node (Tree.node (Tree.leaf 4) (Tree.leaf 6)) (Tree.node (Tree.leaf 5) (Tree.leaf 7))) ∧ s = (Tree.node (Tree.node (Tree.leaf 4) (Tree.leaf 5)) (Tree.node (Tree.leaf 6) (Tree.leaf 7))) then (if ([[4, 5], [6], [7]] : Forest).length-1 ≤ b then some [[4, 5], [6], [7]] else none) else (none))
#eval IO.println ("CASE:two-hard-q4|" ++ (callerJSON T0 S0 [[0, 1, 2, 3], [4, 5, 6, 7]] 4 callback0).compress)
def T1 : Tree := (Tree.node (Tree.node (Tree.node (Tree.leaf 0) (Tree.leaf 2)) (Tree.node (Tree.leaf 1) (Tree.leaf 3))) (Tree.node (Tree.node (Tree.leaf 4) (Tree.leaf 6)) (Tree.node (Tree.leaf 5) (Tree.leaf 7))))
def S1 : Tree := (Tree.node (Tree.node (Tree.node (Tree.leaf 0) (Tree.leaf 1)) (Tree.node (Tree.leaf 2) (Tree.leaf 3))) (Tree.node (Tree.node (Tree.leaf 4) (Tree.leaf 5)) (Tree.node (Tree.leaf 6) (Tree.leaf 7))))
def callback1 (t s : Tree) (b : Nat) : Option Forest := if t = (Tree.node (Tree.node (Tree.leaf 0) (Tree.leaf 2)) (Tree.node (Tree.leaf 1) (Tree.leaf 3))) ∧ s = (Tree.node (Tree.node (Tree.leaf 0) (Tree.leaf 1)) (Tree.node (Tree.leaf 2) (Tree.leaf 3))) then (if ([[0, 1], [2], [3]] : Forest).length-1 ≤ b then some [[0, 1], [2], [3]] else none) else (if t = (Tree.node (Tree.node (Tree.leaf 4) (Tree.leaf 6)) (Tree.node (Tree.leaf 5) (Tree.leaf 7))) ∧ s = (Tree.node (Tree.node (Tree.leaf 4) (Tree.leaf 5)) (Tree.node (Tree.leaf 6) (Tree.leaf 7))) then (if ([[4, 5], [6], [7]] : Forest).length-1 ≤ b then some [[4, 5], [6], [7]] else none) else (none))
#eval IO.println ("CASE:two-hard-q3-reject|" ++ (callerJSON T1 S1 [[0, 1, 2, 3], [4, 5, 6, 7]] 3 callback1).compress)
def T2 : Tree := (Tree.node (Tree.node (Tree.node (Tree.leaf 0) (Tree.leaf 2)) (Tree.node (Tree.leaf 1) (Tree.leaf 3))) (Tree.node (Tree.node (Tree.leaf 4) (Tree.leaf 6)) (Tree.node (Tree.leaf 5) (Tree.leaf 7))))
def S2 : Tree := (Tree.node (Tree.node (Tree.node (Tree.leaf 0) (Tree.leaf 1)) (Tree.node (Tree.leaf 2) (Tree.leaf 3))) (Tree.node (Tree.node (Tree.leaf 4) (Tree.leaf 5)) (Tree.node (Tree.leaf 6) (Tree.leaf 7))))
def callback2 (t s : Tree) (b : Nat) : Option Forest := if t = (Tree.node (Tree.node (Tree.leaf 0) (Tree.leaf 2)) (Tree.node (Tree.leaf 1) (Tree.leaf 3))) ∧ s = (Tree.node (Tree.node (Tree.leaf 0) (Tree.leaf 1)) (Tree.node (Tree.leaf 2) (Tree.leaf 3))) then (if ([[0, 1], [2], [3]] : Forest).length-1 ≤ b then some [[0, 1], [2], [3]] else none) else (if t = (Tree.node (Tree.node (Tree.leaf 4) (Tree.leaf 6)) (Tree.node (Tree.leaf 5) (Tree.leaf 7))) ∧ s = (Tree.node (Tree.node (Tree.leaf 4) (Tree.leaf 5)) (Tree.node (Tree.leaf 6) (Tree.leaf 7))) then (if ([[4, 5], [6], [7]] : Forest).length-1 ≤ b then some [[4, 5], [6], [7]] else none) else (none))
#eval IO.println ("CASE:two-hard-q5|" ++ (callerJSON T2 S2 [[0, 1, 2, 3], [4, 5, 6, 7]] 5 callback2).compress)
def T3 : Tree := (Tree.node (Tree.node (Tree.node (Tree.leaf 0) (Tree.leaf 2)) (Tree.node (Tree.leaf 1) (Tree.leaf 3))) (Tree.node (Tree.node (Tree.leaf 4) (Tree.leaf 6)) (Tree.node (Tree.leaf 5) (Tree.leaf 7))))
def S3 : Tree := (Tree.node (Tree.node (Tree.node (Tree.leaf 0) (Tree.leaf 1)) (Tree.node (Tree.leaf 2) (Tree.leaf 3))) (Tree.node (Tree.node (Tree.leaf 4) (Tree.leaf 5)) (Tree.node (Tree.leaf 6) (Tree.leaf 7))))
def callback3 (t s : Tree) (b : Nat) : Option Forest := if t = (Tree.node (Tree.node (Tree.leaf 0) (Tree.leaf 2)) (Tree.node (Tree.leaf 1) (Tree.leaf 3))) ∧ s = (Tree.node (Tree.node (Tree.leaf 0) (Tree.leaf 1)) (Tree.node (Tree.leaf 2) (Tree.leaf 3))) then (if ([[0, 1], [2], [3]] : Forest).length-1 ≤ b then some [[0, 1], [2], [3]] else none) else (if t = (Tree.node (Tree.node (Tree.leaf 4) (Tree.leaf 6)) (Tree.node (Tree.leaf 5) (Tree.leaf 7))) ∧ s = (Tree.node (Tree.node (Tree.leaf 4) (Tree.leaf 5)) (Tree.node (Tree.leaf 6) (Tree.leaf 7))) then (if ([[4, 5], [6], [7]] : Forest).length-1 ≤ b then some [[4, 5], [6], [7]] else none) else (none))
#eval IO.println ("CASE:duplicate-slot-identities|" ++ (callerJSON T3 S3 [[0, 1, 2, 3], [4, 5, 6, 7]] 4 callback3).compress)
def T4 : Tree := (Tree.node (Tree.node (Tree.node (Tree.leaf 0) (Tree.leaf 2)) (Tree.node (Tree.leaf 1) (Tree.leaf 3))) (Tree.node (Tree.node (Tree.leaf 4) (Tree.leaf 6)) (Tree.node (Tree.leaf 5) (Tree.leaf 7))))
def S4 : Tree := (Tree.node (Tree.node (Tree.node (Tree.leaf 0) (Tree.leaf 1)) (Tree.node (Tree.leaf 2) (Tree.leaf 3))) (Tree.node (Tree.node (Tree.leaf 4) (Tree.leaf 5)) (Tree.node (Tree.leaf 6) (Tree.leaf 7))))
def callback4 (t s : Tree) (b : Nat) : Option Forest := if t = (Tree.node (Tree.node (Tree.leaf 4) (Tree.leaf 6)) (Tree.node (Tree.leaf 5) (Tree.leaf 7))) ∧ s = (Tree.node (Tree.node (Tree.leaf 4) (Tree.leaf 5)) (Tree.node (Tree.leaf 6) (Tree.leaf 7))) then (if ([[4, 5], [6], [7]] : Forest).length-1 ≤ b then some [[4, 5], [6], [7]] else none) else (if t = (Tree.node (Tree.node (Tree.leaf 0) (Tree.leaf 2)) (Tree.node (Tree.leaf 1) (Tree.leaf 3))) ∧ s = (Tree.node (Tree.node (Tree.leaf 0) (Tree.leaf 1)) (Tree.node (Tree.leaf 2) (Tree.leaf 3))) then (if ([[0, 1], [2], [3]] : Forest).length-1 ≤ b then some [[0, 1], [2], [3]] else none) else (none))
#eval IO.println ("CASE:reordered-Q|" ++ (callerJSON T4 S4 [[4, 5, 6, 7], [0, 1, 2, 3]] 4 callback4).compress)
def T5 : Tree := (Tree.node (Tree.node (Tree.node (Tree.leaf 0) (Tree.leaf 2)) (Tree.node (Tree.leaf 1) (Tree.leaf 3))) (Tree.node (Tree.node (Tree.leaf 4) (Tree.leaf 6)) (Tree.node (Tree.leaf 5) (Tree.leaf 7))))
def S5 : Tree := (Tree.node (Tree.node (Tree.node (Tree.leaf 0) (Tree.leaf 1)) (Tree.node (Tree.leaf 2) (Tree.leaf 3))) (Tree.node (Tree.node (Tree.leaf 4) (Tree.leaf 5)) (Tree.node (Tree.leaf 6) (Tree.leaf 7))))
def callback5 (t s : Tree) (b : Nat) : Option Forest := if t = (Tree.node (Tree.node (Tree.leaf 0) (Tree.leaf 2)) (Tree.node (Tree.leaf 1) (Tree.leaf 3))) ∧ s = (Tree.node (Tree.node (Tree.leaf 0) (Tree.leaf 1)) (Tree.node (Tree.leaf 2) (Tree.leaf 3))) then none else (if t = (Tree.node (Tree.node (Tree.leaf 4) (Tree.leaf 6)) (Tree.node (Tree.leaf 5) (Tree.leaf 7))) ∧ s = (Tree.node (Tree.node (Tree.leaf 4) (Tree.leaf 5)) (Tree.node (Tree.leaf 6) (Tree.leaf 7))) then (if ([[4, 5], [6], [7]] : Forest).length-1 ≤ b then some [[4, 5], [6], [7]] else none) else (none))
#eval IO.println ("CASE:first-recursive-failure|" ++ (callerJSON T5 S5 [[0, 1, 2, 3], [4, 5, 6, 7]] 4 callback5).compress)
def T6 : Tree := (Tree.node (Tree.node (Tree.node (Tree.leaf 0) (Tree.leaf 2)) (Tree.node (Tree.leaf 1) (Tree.leaf 3))) (Tree.node (Tree.node (Tree.leaf 4) (Tree.leaf 6)) (Tree.node (Tree.leaf 5) (Tree.leaf 7))))
def S6 : Tree := (Tree.node (Tree.node (Tree.node (Tree.leaf 0) (Tree.leaf 1)) (Tree.node (Tree.leaf 2) (Tree.leaf 3))) (Tree.node (Tree.node (Tree.leaf 4) (Tree.leaf 5)) (Tree.node (Tree.leaf 6) (Tree.leaf 7))))
def callback6 (t s : Tree) (b : Nat) : Option Forest := if t = (Tree.node (Tree.node (Tree.leaf 0) (Tree.leaf 2)) (Tree.node (Tree.leaf 1) (Tree.leaf 3))) ∧ s = (Tree.node (Tree.node (Tree.leaf 0) (Tree.leaf 1)) (Tree.node (Tree.leaf 2) (Tree.leaf 3))) then (if ([[0], [1], [2], [3]] : Forest).length-1 ≤ b then some [[0], [1], [2], [3]] else none) else (if t = (Tree.node (Tree.node (Tree.leaf 4) (Tree.leaf 6)) (Tree.node (Tree.leaf 5) (Tree.leaf 7))) ∧ s = (Tree.node (Tree.node (Tree.leaf 4) (Tree.leaf 5)) (Tree.node (Tree.leaf 6) (Tree.leaf 7))) then (if ([[4], [5], [6], [7]] : Forest).length-1 ≤ b then some [[4], [5], [6], [7]] else none) else (none))
#eval IO.println ("CASE:individually-ok-joint-over-budget|" ++ (callerJSON T6 S6 [[0, 1, 2, 3], [4, 5, 6, 7]] 5 callback6).compress)
def T7 : Tree := (Tree.node (Tree.node (Tree.node (Tree.leaf 0) (Tree.leaf 2)) (Tree.leaf 1)) (Tree.node (Tree.node (Tree.leaf 3) (Tree.leaf 5)) (Tree.node (Tree.leaf 4) (Tree.leaf 6))))
def S7 : Tree := (Tree.node (Tree.node (Tree.node (Tree.leaf 0) (Tree.leaf 1)) (Tree.leaf 2)) (Tree.node (Tree.node (Tree.leaf 3) (Tree.leaf 4)) (Tree.node (Tree.leaf 5) (Tree.leaf 6))))
def callback7 (t s : Tree) (b : Nat) : Option Forest := if t = (Tree.node (Tree.node (Tree.leaf 0) (Tree.leaf 2)) (Tree.leaf 1)) ∧ s = (Tree.node (Tree.node (Tree.leaf 0) (Tree.leaf 1)) (Tree.leaf 2)) then (if ([[0, 1], [2]] : Forest).length-1 ≤ b then some [[0, 1], [2]] else none) else (if t = (Tree.node (Tree.node (Tree.leaf 3) (Tree.leaf 5)) (Tree.node (Tree.leaf 4) (Tree.leaf 6))) ∧ s = (Tree.node (Tree.node (Tree.leaf 3) (Tree.leaf 4)) (Tree.node (Tree.leaf 5) (Tree.leaf 6))) then (if ([[3, 4], [5], [6]] : Forest).length-1 ≤ b then some [[3, 4], [5], [6]] else none) else (none))
#eval IO.println ("CASE:stored-one-hard-two|" ++ (callerJSON T7 S7 [[0, 1, 2], [3, 4, 5, 6]] 3 callback7).compress)
def T8 : Tree := (Tree.node (Tree.node (Tree.node (Tree.leaf 0) (Tree.leaf 2)) (Tree.leaf 1)) (Tree.node (Tree.node (Tree.leaf 3) (Tree.leaf 5)) (Tree.node (Tree.leaf 4) (Tree.leaf 6))))
def S8 : Tree := (Tree.node (Tree.node (Tree.node (Tree.leaf 0) (Tree.leaf 1)) (Tree.leaf 2)) (Tree.node (Tree.node (Tree.leaf 3) (Tree.leaf 4)) (Tree.node (Tree.leaf 5) (Tree.leaf 6))))
def callback8 (t s : Tree) (b : Nat) : Option Forest := if t = (Tree.node (Tree.node (Tree.leaf 0) (Tree.leaf 2)) (Tree.leaf 1)) ∧ s = (Tree.node (Tree.node (Tree.leaf 0) (Tree.leaf 1)) (Tree.leaf 2)) then (if ([[0, 1], [2]] : Forest).length-1 ≤ b then some [[0, 1], [2]] else none) else (if t = (Tree.node (Tree.node (Tree.leaf 3) (Tree.leaf 5)) (Tree.node (Tree.leaf 4) (Tree.leaf 6))) ∧ s = (Tree.node (Tree.node (Tree.leaf 3) (Tree.leaf 4)) (Tree.node (Tree.leaf 5) (Tree.leaf 6))) then (if ([[3, 4], [5], [6]] : Forest).length-1 ≤ b then some [[3, 4], [5], [6]] else none) else (none))
#eval IO.println ("CASE:stored-one-reject-q2|" ++ (callerJSON T8 S8 [[0, 1, 2], [3, 4, 5, 6]] 2 callback8).compress)
def T9 : Tree := (Tree.node (Tree.node (Tree.node (Tree.leaf 0) (Tree.leaf 2)) (Tree.node (Tree.leaf 1) (Tree.leaf 3))) (Tree.leaf 4))
def S9 : Tree := (Tree.node (Tree.node (Tree.node (Tree.leaf 0) (Tree.leaf 1)) (Tree.node (Tree.leaf 2) (Tree.leaf 3))) (Tree.leaf 4))
def callback9 (t s : Tree) (b : Nat) : Option Forest := if t = (Tree.node (Tree.node (Tree.leaf 0) (Tree.leaf 2)) (Tree.node (Tree.leaf 1) (Tree.leaf 3))) ∧ s = (Tree.node (Tree.node (Tree.leaf 0) (Tree.leaf 1)) (Tree.node (Tree.leaf 2) (Tree.leaf 3))) then (if ([[0, 1], [2], [3]] : Forest).length-1 ≤ b then some [[0, 1], [2], [3]] else none) else (if t = (Tree.leaf 4) ∧ s = (Tree.leaf 4) then (if ([[4]] : Forest).length-1 ≤ b then some [[4]] else none) else (none))
#eval IO.println ("CASE:hard-plus-zero|" ++ (callerJSON T9 S9 [[0, 1, 2, 3], [4]] 2 callback9).compress)
def T10 : Tree := (Tree.node (Tree.node (Tree.leaf 0) (Tree.leaf 2)) (Tree.node (Tree.leaf 1) (Tree.leaf 3)))
def S10 : Tree := (Tree.node (Tree.node (Tree.leaf 0) (Tree.leaf 1)) (Tree.node (Tree.leaf 2) (Tree.leaf 3)))
def callback10 (t s : Tree) (b : Nat) : Option Forest := if t = (Tree.node (Tree.node (Tree.leaf 0) (Tree.leaf 2)) (Tree.node (Tree.leaf 1) (Tree.leaf 3))) ∧ s = (Tree.node (Tree.node (Tree.leaf 0) (Tree.leaf 1)) (Tree.node (Tree.leaf 2) (Tree.leaf 3))) then (if ([[0, 1], [2], [3]] : Forest).length-1 ≤ b then some [[0, 1], [2], [3]] else none) else (none)
#eval IO.println ("CASE:sole-hard-no-discount|" ++ (callerJSON T10 S10 [[0, 1, 2, 3]] 2 callback10).compress)
def T11 : Tree := (Tree.node (Tree.node (Tree.leaf 0) (Tree.leaf 1)) (Tree.leaf 2))
def S11 : Tree := (Tree.node (Tree.node (Tree.leaf 0) (Tree.leaf 1)) (Tree.leaf 2))
def callback11 (t s : Tree) (b : Nat) : Option Forest := if t = (Tree.node (Tree.leaf 0) (Tree.leaf 1)) ∧ s = (Tree.node (Tree.leaf 0) (Tree.leaf 1)) then (if ([[0, 1]] : Forest).length-1 ≤ b then some [[0, 1]] else none) else (if t = (Tree.leaf 2) ∧ s = (Tree.leaf 2) then (if ([[2]] : Forest).length-1 ≤ b then some [[2]] else none) else (none))
#eval IO.println ("CASE:resolved-zero-q0|" ++ (callerJSON T11 S11 [[0, 1], [2]] 0 callback11).compress)
def T12 : Tree := (Tree.node (Tree.node (Tree.node (Tree.leaf 0) (Tree.leaf 2)) (Tree.leaf 1)) (Tree.leaf 3))
def S12 : Tree := (Tree.node (Tree.node (Tree.node (Tree.leaf 0) (Tree.leaf 1)) (Tree.leaf 2)) (Tree.leaf 3))
def callback12 (t s : Tree) (b : Nat) : Option Forest := if t = (Tree.node (Tree.node (Tree.leaf 0) (Tree.leaf 2)) (Tree.leaf 1)) ∧ s = (Tree.node (Tree.node (Tree.leaf 0) (Tree.leaf 1)) (Tree.leaf 2)) then (if ([[0, 1], [2]] : Forest).length-1 ≤ b then some [[0, 1], [2]] else none) else (if t = (Tree.leaf 3) ∧ s = (Tree.leaf 3) then (if ([[3]] : Forest).length-1 ≤ b then some [[3]] else none) else (none))
#eval IO.println ("CASE:resolved-one-no-query|" ++ (callerJSON T12 S12 [[0, 1, 2], [3]] 1 callback12).compress)
def T13 : Tree := (Tree.node (Tree.node (Tree.leaf 9) (Tree.leaf 7)) (Tree.node (Tree.leaf 2) (Tree.leaf 1)))
def S13 : Tree := (Tree.node (Tree.node (Tree.leaf 9) (Tree.leaf 2)) (Tree.node (Tree.leaf 7) (Tree.leaf 1)))
def callback13 (t s : Tree) (b : Nat) : Option Forest := if t = (Tree.node (Tree.node (Tree.leaf 9) (Tree.leaf 7)) (Tree.node (Tree.leaf 2) (Tree.leaf 1))) ∧ s = (Tree.node (Tree.node (Tree.leaf 9) (Tree.leaf 2)) (Tree.node (Tree.leaf 7) (Tree.leaf 1))) then (if ([[9, 2], [7], [1]] : Forest).length-1 ≤ b then some [[9, 2], [7], [1]] else none) else (none)
#eval IO.println ("CASE:arbitrary-label-sole-hard|" ++ (callerJSON T13 S13 [[9, 2, 7, 1]] 2 callback13).compress)
#eval IO.println ("BAD:absent-request|" ++ (callerJSON (Tree.node (Tree.node (Tree.leaf 0) (Tree.leaf 1)) (Tree.node (Tree.leaf 2) (Tree.leaf 3))) (Tree.node (Tree.node (Tree.leaf 0) (Tree.leaf 1)) (Tree.node (Tree.leaf 2) (Tree.leaf 3))) [[0, 1, 99], [2, 3]] 5 (fun _ _ _ => none)).compress)
#eval IO.println ("BAD:duplicate-request-label|" ++ (callerJSON (Tree.node (Tree.node (Tree.leaf 0) (Tree.leaf 1)) (Tree.node (Tree.leaf 2) (Tree.leaf 3))) (Tree.node (Tree.node (Tree.leaf 0) (Tree.leaf 1)) (Tree.node (Tree.leaf 2) (Tree.leaf 3))) [[0, 1, 1], [2, 3]] 5 (fun _ _ _ => none)).compress)
#eval IO.println ("BAD:missing-request-label|" ++ (callerJSON (Tree.node (Tree.node (Tree.leaf 0) (Tree.leaf 1)) (Tree.node (Tree.leaf 2) (Tree.leaf 3))) (Tree.node (Tree.node (Tree.leaf 0) (Tree.leaf 1)) (Tree.node (Tree.leaf 2) (Tree.leaf 3))) [[0], [2, 3]] 5 (fun _ _ _ => none)).compress)
#eval IO.println ("BAD:empty-request|" ++ (callerJSON (Tree.node (Tree.node (Tree.leaf 0) (Tree.leaf 1)) (Tree.node (Tree.leaf 2) (Tree.leaf 3))) (Tree.node (Tree.node (Tree.leaf 0) (Tree.leaf 1)) (Tree.node (Tree.leaf 2) (Tree.leaf 3))) [[0, 1], [], [2, 3]] 5 (fun _ _ _ => none)).compress)
#eval IO.println ("BAD:duplicate-original-label|" ++ (callerJSON (Tree.node (Tree.node (Tree.leaf 0) (Tree.leaf 1)) (Tree.node (Tree.leaf 2) (Tree.leaf 3))) (Tree.node (Tree.node (Tree.leaf 0) (Tree.leaf 0)) (Tree.node (Tree.leaf 2) (Tree.leaf 3))) [[0, 1], [2, 3]] 5 (fun _ _ _ => none)).compress)
#eval IO.println ("BAD:unequal-original-labels|" ++ (callerJSON (Tree.node (Tree.node (Tree.node (Tree.leaf 0) (Tree.leaf 2)) (Tree.node (Tree.leaf 1) (Tree.leaf 3))) (Tree.node (Tree.node (Tree.leaf 4) (Tree.leaf 6)) (Tree.node (Tree.leaf 5) (Tree.leaf 8)))) (Tree.node (Tree.node (Tree.node (Tree.leaf 0) (Tree.leaf 1)) (Tree.node (Tree.leaf 2) (Tree.leaf 3))) (Tree.node (Tree.node (Tree.leaf 4) (Tree.leaf 5)) (Tree.node (Tree.leaf 6) (Tree.leaf 7)))) [[0, 1, 2, 3], [4, 5, 6, 7]] 5 (fun _ _ _ => none)).compress)
#eval IO.println ("BAD:target-guard-only|" ++ (callerJSON (Tree.node (Tree.node (Tree.leaf 0) (Tree.leaf 1)) (Tree.node (Tree.leaf 2) (Tree.leaf 3))) (Tree.node (Tree.node (Tree.leaf 0) (Tree.leaf 2)) (Tree.node (Tree.leaf 1) (Tree.leaf 3))) [[0, 2], [1, 3]] 5 (fun _ _ _ => none)).compress)
#eval IO.println ("BAD:source-guard-only|" ++ (callerJSON (Tree.node (Tree.node (Tree.leaf 0) (Tree.leaf 2)) (Tree.node (Tree.leaf 1) (Tree.leaf 3))) (Tree.node (Tree.node (Tree.leaf 0) (Tree.leaf 1)) (Tree.node (Tree.leaf 2) (Tree.leaf 3))) [[0, 2], [1, 3]] 5 (fun _ _ _ => none)).compress)
#eval IO.println ("DUPLICATE:generic-slots|" ++ (toJson ((schedule (fun (_ : String) (_ : Nat) => some (2,(0 : Nat))) 4 [Job.hard "same",Job.hard "same"]).calls)).compress)
