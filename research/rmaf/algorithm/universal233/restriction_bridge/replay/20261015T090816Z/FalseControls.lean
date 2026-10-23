import Controls
open RMAF RestrictionBridge.Controls
example : (restrict [0,1] T).bind (restrict [1]) ≠ restrict [1] T := by decide
example : [] ∈ minimalVertices [0,1] T := by decide
example : agreement T T Qbad = true := by decide
example : refines Q F = true := by decide
example : (Q.map (fun U => (subfamily U F).length - 1)).sum = F.length - 1 := by decide
