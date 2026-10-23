import RestrictionTolls
open TripleDP.Transitions.Restriction TripleDP.Transitions.Restriction.Fixtures
example : R7.cost - ((restrict R7 H7 false).cost + (restrict R7 H7 true).cost) = 1 := by
  rw [extend_unused_toll]
  decide
