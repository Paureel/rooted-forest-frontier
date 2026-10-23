import Lean
import CoreProgram
open RMAF Universal233.CoreProgram Lean

def configs : List (String × Tree × List (Nat × Nat) × Nat) := [
  ("outscope-overlapping-source-parents/LA", (.node (.node (.node (.node (.node (.leaf 1) (.node (.leaf 4) (.leaf 6))) (.node (.leaf 5) (.leaf 7))) (.leaf 2)) (.leaf 3)) (.leaf 8)), [(1, 0), (2, 1), (3, 1), (4, 2), (5, 2), (6, 2), (7, 2), (8, 3)], 7),
  ("outscope-overlapping-source-parents/LB", (.node (.node (.node (.node (.node (.leaf 1) (.node (.leaf 4) (.leaf 6))) (.node (.leaf 5) (.leaf 7))) (.leaf 2)) (.leaf 3)) (.leaf 8)), [(1, 0), (2, 0), (3, 0), (4, 1), (5, 1), (6, 2), (7, 2), (8, 3)], 7)
]

def addr (p : Vertex) : String := String.join (p.map (fun b => if b then "1" else "0"))
def outputJson (o : Output) : Json := Json.mkObj [
  ("partition", toJson o.partition), ("sourceCuts", toJson (o.sourceCuts.map addr))]
def receiptJson (r : Receipt) : Json := Json.mkObj [
  ("outputs", Json.arr (r.outputs.map outputJson).toArray),
  ("refusals", toJson r.refusals), ("visited", toJson r.visited),
  ("childAttempts", toJson r.childAttempts), ("pruned", toJson r.pruned)]
def main : IO Unit := do
  for (name,t,colors,qmax) in configs do
    let col := fun x => ((colors.find? (fun z => z.1 == x)).map Prod.snd).getD 99
    for q in List.range (qmax + 1) do
      let j := Json.mkObj [("id",toJson name),("q",toJson q), ("receipt",receiptJson (generate t col q))]
      IO.println j.compress
