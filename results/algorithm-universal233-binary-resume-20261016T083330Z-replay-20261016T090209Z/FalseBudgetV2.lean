import ProviderResumeControls
open GenericForest.BinaryProvider GenericForest.BinaryProvider.ResumeControls GenericForest.BinaryProvider.Controls GenericForest.ScalarBits
example : (checkerFromInput (some pair) [pair] [] [[one],[two]]).value=some [[one],[two]] := by rw [checker_budget.1];decide
