import RestrictionTolls
open TripleDP.Transitions.Restriction TripleDP.Transitions.Restriction.Fixtures
example : (restrict R6 H6 false).cost = 1 := by
  rw [unused_root_child_cost]
  decide
