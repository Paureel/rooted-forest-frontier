import Controls
open RMAF Universal233.HardParent

-- Five false propositions must fail. This module is never imported by a proof.
example : agreement target4 source4 [[0,1,2],[3]] = true := by decide
example : pairwiseEmbeddings target4 [[0,2],[1,3]] = true := by decide
example : (4 : Nat) ∉ ([0,1,4] : List Nat) := by decide
example : agreement target4 (.node (.node (.leaf 0) (.leaf 2)) (.node (.leaf 1) (.leaf 2))) [[0,1],[2],[3]] = true := by decide
example : literalThree source4 [false,true] [true,true] = [[2],[3],[]] := by decide
