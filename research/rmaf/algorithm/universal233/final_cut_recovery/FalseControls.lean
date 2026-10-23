import RecoveryProgram
open RMAF Universal233.CoreProgram Universal233.FinalCutRecovery
-- These propositions deliberately fail and must never elaborate.
theorem false_cut_list : recover
    (.node (.leaf 91) (.node (.leaf 7) (.node (.leaf 55) (.leaf 3))))
    [[3,55],[91],[7]] = some ⟨[[7],[91],[55,3]],[[true],[false]]⟩ := by decide

theorem false_embedding_acceptance : inputCheck
    (.node (.node (.leaf 41) (.leaf 7)) (.node (.leaf 99) (.leaf 12)))
    [[41,99],[7,12]] = true := by decide

theorem false_statement : False := by decide
