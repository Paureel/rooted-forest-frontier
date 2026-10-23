import Lean
import CoreProgram
open RMAF Universal233.CoreProgram Lean

def configs : List (String × Tree × List (Nat × Nat) × Nat) := [
  ("surrounding-A-good-sectors/LA", (.node (.node (.node (.leaf 1) (.node (.leaf 2) (.node (.node (.leaf 4) (.leaf 6)) (.node (.leaf 5) (.leaf 7))))) (.leaf 3)) (.leaf 8)), [(1, 0), (2, 1), (3, 1), (4, 2), (5, 2), (6, 2), (7, 2), (8, 3)], 7),
  ("surrounding-A-good-sectors/LB", (.node (.node (.node (.leaf 1) (.node (.leaf 2) (.node (.node (.leaf 4) (.leaf 6)) (.node (.leaf 5) (.leaf 7))))) (.leaf 3)) (.leaf 8)), [(1, 0), (2, 0), (3, 0), (4, 1), (5, 1), (6, 2), (7, 2), (8, 3)], 7),
  ("surrounding-A-right-attachment/LA", (.node (.node (.node (.leaf 1) (.node (.leaf 2) (.leaf 3))) (.node (.node (.leaf 4) (.leaf 6)) (.node (.leaf 5) (.leaf 7)))) (.leaf 8)), [(1, 0), (2, 0), (3, 1), (4, 2), (5, 2), (6, 2), (7, 2), (8, 3)], 7),
  ("surrounding-A-right-attachment/LB", (.node (.node (.node (.leaf 1) (.node (.leaf 2) (.leaf 3))) (.node (.node (.leaf 4) (.leaf 6)) (.node (.leaf 5) (.leaf 7)))) (.leaf 8)), [(1, 0), (2, 0), (3, 0), (4, 1), (5, 1), (6, 2), (7, 2), (8, 3)], 7),
  ("cheap-bad-A-sector/LA", (.node (.node (.node (.node (.node (.leaf 1) (.leaf 2)) (.leaf 3)) (.leaf 4)) (.node (.node (.leaf 5) (.leaf 7)) (.node (.leaf 6) (.leaf 8)))) (.leaf 9)), [(1, 0), (2, 0), (3, 0), (4, 1), (5, 2), (6, 2), (7, 2), (8, 2), (9, 3)], 8),
  ("cheap-bad-A-sector/LB", (.node (.node (.node (.node (.node (.leaf 1) (.leaf 2)) (.leaf 3)) (.leaf 4)) (.node (.node (.leaf 5) (.leaf 7)) (.node (.leaf 6) (.leaf 8)))) (.leaf 9)), [(1, 0), (2, 0), (3, 0), (4, 0), (5, 1), (6, 1), (7, 2), (8, 2), (9, 3)], 8),
  ("both-high-crossed/LA", (.node (.node (.node (.node (.leaf 1) (.leaf 3)) (.node (.leaf 2) (.leaf 4))) (.node (.node (.leaf 5) (.leaf 7)) (.node (.leaf 6) (.leaf 8)))) (.leaf 9)), [(1, 0), (2, 0), (3, 1), (4, 1), (5, 2), (6, 2), (7, 2), (8, 2), (9, 3)], 8),
  ("both-high-crossed/LB", (.node (.node (.node (.node (.leaf 1) (.leaf 3)) (.node (.leaf 2) (.leaf 4))) (.node (.node (.leaf 5) (.leaf 7)) (.node (.leaf 6) (.leaf 8)))) (.leaf 9)), [(1, 0), (2, 0), (3, 0), (4, 0), (5, 1), (6, 1), (7, 2), (8, 2), (9, 3)], 8),
  ("public-good-A-conditional-E/LA", (.node (.node (.node (.leaf 1) (.leaf 2)) (.node (.node (.leaf 3) (.leaf 5)) (.node (.leaf 4) (.leaf 6)))) (.leaf 7)), [(1, 0), (2, 1), (3, 2), (4, 2), (5, 2), (6, 2), (7, 3)], 6),
  ("public-good-A-conditional-E/LB", (.node (.node (.node (.leaf 1) (.leaf 2)) (.node (.node (.leaf 3) (.leaf 5)) (.node (.leaf 4) (.leaf 6)))) (.leaf 7)), [(1, 0), (2, 0), (3, 1), (4, 1), (5, 2), (6, 2), (7, 3)], 6)
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
