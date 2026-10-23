import ValidPartition
open RMAF Universal233.CoreGraph Universal233.CutRealization
example : Adj (.node (.leaf 0) (.leaf 1)) [] [false] := by simp [Adj,Valid,subtree]
example : ¬ Adj (.node (.node (.leaf 0) (.leaf 1)) (.leaf 2)) [] [false,true] := by simp [Adj,Valid,subtree]
example : ¬ ResidualAdj (.node (.leaf 0) (.leaf 1)) [[false],[true]] [] [false] := by simp [ResidualAdj,Adj,Valid,subtree]
