import ForestResource
import Lean
open Lean Universal233.PaidQueries

def table (second p b : Nat) : Option (Nat × Nat) :=
  let m := if p=0 then 2 else second
  if m≤b then some (m,p) else none

def row (id : String) (second q : Nat) : Json :=
  let js : List (Job Nat Nat) := [.hard 0,.hard 1]
  let r := meterSchedule (table second) (fun p b => 10+p+b) q js
  Json.mkObj [("id",toJson id),("calls",toJson r.value.calls),("queries",toJson r.queries),
    ("answers",toJson r.value.answers),("recursiveWork",toJson r.recursiveWork),
    ("callerWork",toJson r.callerWork)]

def main (args : List String) : IO UInt32 := do
  if args.length != 2 then return 2
  let rows := if args[0]! == "pilot" then [row "equal_success" 2 4] else
    [row "equal_refusal" 2 3,row "equal_success" 2 4,row "second_failure" 3 4,row "mixed_success" 3 5]
  IO.FS.writeFile args[1]! ((toJson rows).pretty++"\n")
  return 0
