import RestrictionTolls
open TripleDP.Transitions.Restriction TripleDP.Transitions.Restriction.Fixtures
example : (restrict R5 H5 false).cost = 1 := by
  rw [closed_root_child_cost]
  decide
