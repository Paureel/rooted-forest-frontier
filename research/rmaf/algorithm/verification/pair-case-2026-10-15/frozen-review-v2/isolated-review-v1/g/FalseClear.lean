import Controls
open PairGeometry PairGeometry.Controls
-- Binary side colors alone do not imply full mutual clearance.
theorem planted_false_clear : edgeOK ternary [0,1,2] [3,4] ([],[true])=true := by decide
