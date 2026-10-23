import PairWitness
import Lean
open Lean Universal233.CoreProgram Universal233.ScaffoldWitness

def outJson (o : Output) : Json := Json.mkObj [
  ("partition", toJson o.partition),
  ("sourceCuts", toJson (o.sourceCuts.map (fun p => p.map (fun b => if b then (1 : Nat) else 0))))]

def receiptJson (r : Receipt) : Json := Json.mkObj [
  ("outputs", Json.arr (r.outputs.map outJson).toArray),
  ("refusals", toJson r.refusals), ("visited", toJson r.visited),
  ("childAttempts", toJson r.childAttempts), ("pruned", toJson r.pruned)]

#eval IO.println ("PRODJSON|A|" ++ (receiptJson actualA).compress)
#eval IO.println ("PRODJSON|ASwap|" ++ (receiptJson (generate sourceA (fun x => 1 - aColor x) 2)).compress)
#eval IO.println ("PRODJSON|B|" ++ (receiptJson (generate (.node (.leaf 4) (.leaf 5)) (fun x => if x = 4 then 0 else 1) 1)).compress)
#eval IO.println ("PRODJSON|BSwap|" ++ (receiptJson (generate (.node (.leaf 4) (.leaf 5)) (fun x => if x = 4 then 1 else 0) 1)).compress)
#eval IO.println ("PRODJSON|AUnderBudget|" ++ (receiptJson (generate sourceA aColor 1)).compress)
