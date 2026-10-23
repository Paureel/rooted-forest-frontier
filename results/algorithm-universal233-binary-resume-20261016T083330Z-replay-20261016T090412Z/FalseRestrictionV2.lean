import ProviderResumeControls
open GenericForest.BinaryProvider GenericForest.BinaryProvider.ResumeControls GenericForest.BinaryProvider.Controls GenericForest.ScalarBits
example : (restrictLabels [one,three] T).value=some (.leaf one) := by rw [restriction_exact.1];decide
