import ChargeControls
open TripleDP.RestrictionCharge
example : closedCharge [0,1,2] (fun i => i < 2) (none : Option Nat) = 1 := by decide
