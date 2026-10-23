import RestrictionTolls
open TripleDP.Transitions.Restriction TripleDP.Transitions.Restriction.Fixtures
example : R1.cost - ((restrict R1 H1 false).cost + (restrict R1 H1 true).cost) = 0 := by
  rw [close_toll]
  decide
