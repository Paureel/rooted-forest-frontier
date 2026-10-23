import Rule4Controls
open RMAF Universal233.Rule4 Universal233.Rule4.Controls
theorem false_strict_cover : ((branches chosen).any (fun b => refinesCheck F b.partition)) = true := by decide
theorem false_unpaid_swap : (branches chosen).map Branch.cost = [2,1,1] := by decide
theorem false_role_source : ((branches chosen)[2]'(by decide)).source = S := by decide
theorem false_outside_clearance : disjointVertices (minimalVertices [0,3] outsideS) (minimalVertices [2,5] outsideS) = true := by decide
theorem false_t1_admitted : (select badT badS).isSome = true := by decide
