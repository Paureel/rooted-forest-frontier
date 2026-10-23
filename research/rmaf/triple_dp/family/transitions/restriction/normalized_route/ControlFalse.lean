import ControlClean
open TripleDP TripleDP.CostRoute
theorem false_right_label : LeafAt (.node (.leaf 7) (.leaf 9)) [true] 7 := by
  change [] = ([] : Address) ∧ 7 = 9
  decide
