import LiteralInterface
open Universal233.PaidLiteralDecisionWork
example : (checksMeter [fun _=>⟨false,3⟩,fun _=>⟨true,100⟩]).work = 4 := by decide +kernel
example : (checksMeter [fun _=>⟨true,3⟩,fun _=>⟨false,5⟩]).work = 10 := by decide +kernel
example : (treeEqMeter (.node (.leaf 1) (.leaf 2)) (.node (.leaf 9) (.leaf 2))).work = 4 := by decide +kernel
example : (orMeter ⟨true,3⟩ (fun _=>⟨true,7⟩)).work = 4 := by decide +kernel
example : (orMeter ⟨false,3⟩ (fun _=>⟨true,7⟩)).work = 11 := by decide +kernel
example : literalBudget 0 = 164 := by decide +kernel
example : literalBudget 1 = 6098 := by decide +kernel
