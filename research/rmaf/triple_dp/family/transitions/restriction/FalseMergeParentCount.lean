import RestrictionTolls
open TripleDP.Transitions.Restriction TripleDP.Transitions.Restriction.Fixtures
example : R4.blockCount = 2 := by
  rw [merge_parent_count]
  decide
