import FreshComparisons
open RMAF Universal233.CoreProgram
example : ((groups (normalize (fromTree (fun x : Nat => if x = 0 then 0 else if x = 1 then 0 else if x = 2 then 1 else 0) [] (.node (.node (.leaf 0) (.leaf 1)) (.leaf 2))))).contains ⟨[false, false], [0], 0⟩) = true := by decide
example : RMAF.pairwiseEmbeddings (.node (.node (.node (.leaf 0) (.leaf 1)) (.leaf 2)) (.node (.leaf 3) (.leaf 4))) [[0, 2], [1, 3, 4]] = true := by decide
