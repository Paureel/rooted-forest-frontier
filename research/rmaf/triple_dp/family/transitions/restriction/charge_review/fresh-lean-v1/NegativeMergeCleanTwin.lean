import ChargeControls
open TripleDP.RestrictionCharge
example : ([0] : List Nat).length + 1 = weight [0] (fun _ => true) + weight [0] (fun _ => true) := by decide
