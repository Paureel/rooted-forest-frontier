import FamilyControls
open TripleDP.Family TripleDP.Family.Controls

-- Same goal and imports as NegativeFamily, with the correct closed cost.
example : closedCost (normalize singletonFamily) = 0 := by
  change (0 : Nat) = 0
  decide
