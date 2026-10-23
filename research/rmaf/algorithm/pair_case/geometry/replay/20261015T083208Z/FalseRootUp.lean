import Controls
open PairGeometry
-- The original root has no artificial upward neighbor.
theorem planted_false_root_up : neighbor [] 2=some [] := by decide
