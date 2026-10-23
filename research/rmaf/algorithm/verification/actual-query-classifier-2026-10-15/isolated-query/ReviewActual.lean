import Work
open Lean Universal233.PaidQueries
def js (x : String) : Json := toJson x
def jobJ (p : Nat × String) : Json := Json.arr #[toJson p.1,toJson p.2]
def witness (p : Nat × String) (m : Nat) : Json := Json.arr #[js "slot",toJson p.1,js p.2,js "minimum",toJson m]
def mock (tag : String) (mins : List Nat) (p : Nat × String) (budget : Nat) : Option (Nat × Json) :=
 let m := mins[p.1]!
 let ok := decide (m ≤ budget)
 dbg_trace ("REVIEW_SPY " ++ (Json.mkObj [("tag",js tag),("index",toJson p.1),("slot",js p.2),("budget",toJson budget),("success",toJson ok),("cost",if ok then toJson m else Json.null),("witness",if ok then witness p m else Json.null)]).compress);
 if ok then some (m,witness p m) else none
def quiet (mins : List Nat) (p : Nat × String) (budget : Nat) : Option (Nat × Json) :=
 let m := mins[p.1]!
 if m ≤ budget then some (m,witness p m) else none
def ansJ (a : Option (List (Nat × Json))) : Json := match a with
 | none => Json.null
 | some xs => toJson (xs.map (fun x => Json.arr #[toJson x.1,x.2]))
def checkQuery (id : String) (q : Nat) (mins : List Nat) (jobs : List (Job (Nat × String) Json)) : IO Unit := do
 let r := schedule (mock (id++":actual") mins) q jobs
 let m := meterSchedule (mock (id++":meter") mins) (fun p b => 100*(p.1+1)+b) q jobs
 let raw := run (quiet mins) (allocated q jobs) jobs
 IO.println ("REVIEW_VALUE " ++ (Json.mkObj [("id",js id),("answers",ansJ r.answers),("rawAnswers",ansJ raw.answers),("calls",toJson r.calls),("visits",toJson r.visits),("known",toJson (knownCost jobs)),("pending",toJson (pending jobs)),("bad",toJson (badSlots jobs)),("budget",toJson (allocated q jobs)),("meterAnswers",ansJ m.value.answers),("meterCalls",toJson m.value.calls),("meterVisits",toJson m.value.visits),("queries",toJson (m.queries.map (fun pb => Json.arr #[jobJ pb.1,toJson pb.2]))),("callerWork",toJson m.callerWork),("recursiveWork",toJson m.recursiveWork),("mass",toJson ([ ("2",actualQueryMass 2 q r.calls),("233/100",actualQueryMass (mkRat 233 100) q r.calls),("3",actualQueryMass 3 q r.calls)].map (fun (k,v) => Json.arr #[js k,js (toString v)])))]).compress)
def main : IO Unit := do
 checkQuery "two-budget3-successes-total6-reject" 5 [3,3] [(.hard (0,"A")),(.hard (1,"B"))]
 checkQuery "known1-one-min4-total5-accept" 5 [4] [(.resolved (0,"R") 1 (js "resolved-r")),(.hard (0,"A"))]
 checkQuery "sole-hard-budget5-no-discount" 5 [5] [(.hard (0,"A"))]
 checkQuery "q3-two-hard-slots-early-no-calls" 3 [2,2] [(.hard (0,"A")),(.hard (1,"B"))]
 checkQuery "q6-three-min2-budget2-all-accept" 6 [2,2,2] [(.hard (0,"A")),(.hard (1,"B")),(.hard (2,"C"))]
 checkQuery "first-failure-is-actual-call-and-stops" 5 [4,2] [(.hard (0,"A")),(.hard (1,"B"))]
 checkQuery "middle-failure-executed-prefix-only" 6 [2,3,2] [(.hard (0,"A")),(.hard (1,"B")),(.hard (2,"C"))]
 checkQuery "last-failure-retains-three-calls" 6 [2,2,3] [(.hard (0,"A")),(.hard (1,"B")),(.hard (2,"C"))]
 checkQuery "no-slots-q0-accept-empty" 0 [] []
 checkQuery "no-unresolved-known5-accept" 5 [] [(.resolved (0,"R") 5 (js "known5"))]
 checkQuery "excess-known-cost-rejects-before-call" 5 [] [(.resolved (0,"R") 6 (js "known6"))]
 checkQuery "zero-resolved-cost-not-bad-slot" 5 [5] [(.resolved (0,"R") 0 (js "zero")),(.hard (0,"A"))]
 checkQuery "two-positive-resolved-slots-zero-mass" 5 [] [(.resolved (0,"R") 1 (js "one")),(.resolved (1,"S") 2 (js "two"))]
 checkQuery "duplicate-slot-ids-retain-position-and-mass" 4 [2,2] [(.hard (0,"X")),(.hard (1,"X"))]
 checkQuery "mixed-known-and-two-hard-budget2" 6 [2,2] [(.resolved (0,"R") 0 (js "zero")),(.resolved (1,"S") 2 (js "two")),(.hard (0,"A")),(.hard (1,"B"))]
 checkQuery "large-q-scalar-budget-preserved" 340282366920938463463374607431768211456 [4] [(.resolved (0,"R") 1 (js "one")),(.hard (0,"A"))]
