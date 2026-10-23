import Controls
open PairGeometry PairGeometry.Controls
-- An absent label cannot satisfy the proper original-input guard.
theorem planted_false_absent : properInput t1 [1,99] b=true := by decide
