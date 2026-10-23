import TripleDP

-- This file MUST fail kernel elaboration: the full bad triple cannot be one
-- region. It is an intentional destructive control and never a library import.
theorem planted_wrong_cost : TripleDP.finish TripleDP.tripleTree = some 1 := by
  decide
