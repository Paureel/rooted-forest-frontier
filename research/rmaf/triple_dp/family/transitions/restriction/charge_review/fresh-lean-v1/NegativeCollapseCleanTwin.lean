import ChargeControls
open TripleDP.RestrictionCharge
example : weight [0,1,2] (fun i => i != 2) = 2 := by decide
