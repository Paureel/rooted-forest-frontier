import Controls
open PairGeometry PairGeometry.Controls VertexGeometry
-- T1's shared vertex has two occupied regions.
theorem planted_false_three : (regions a t1 [false]).length=3 := by decide
