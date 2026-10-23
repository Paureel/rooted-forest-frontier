import CutControls
open RMAF Universal233.CutRealization Universal233.CutRealization.Controls

-- All four propositions are deliberately FALSE and must fail kernel elaboration.
theorem false_wrong_side : leafLabels rootTree [[false]] [false] = [5] := by decide

theorem false_leafless_accepted : leafLabels rootTree [[false],[true]] [] ≠ [] := by decide

theorem false_nested_reabsorbed : 0 ∈ leafLabels nested [p,q] p := by decide

theorem false_suppressed_original_parent : ([false,false,true] : RMAF.Vertex).dropLast = [false] := by decide
