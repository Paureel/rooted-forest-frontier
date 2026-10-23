import ChargeControls
open TripleDP.RestrictionCharge
example : weight [0,1,2] (fun i => i != 2) = 1 := by decide
