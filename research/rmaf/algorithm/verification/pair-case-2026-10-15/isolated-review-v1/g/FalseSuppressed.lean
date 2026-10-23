import Controls
open PairGeometry PairGeometry.Controls
-- A displayed root-to-leaf restriction edge crosses several original edges.
theorem planted_false_suppression : ([],[true,true,true])∈edges trap := by decide
