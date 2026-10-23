import FamilyControls
open TripleDP.Family TripleDP.Family.Controls

-- Deliberate mutant: charging a retained open singleton as a closed region.
example : closedCost (normalize singletonFamily) = 1 := by
  change (0 : Nat) = 1
  decide
