import ParentTransport
open SecondExchange
-- Deliberately incorrect unchanged-edge map: corridor edge 3 is suppressed.
example : splice (splice (fun e : Nat => if e = 3 then some 2 else none) 4 5) 3 5 3 = some 2 := by decide
