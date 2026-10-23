import ChargeControls
open TripleDP.RestrictionCharge
example : closedCharge [0,1] (fun _ => true) (none : Option Nat) = 2 := by decide
