import BinaryCallerControls
open GenericForest.BinaryCaller GenericForest.BinaryCaller.Controls GenericForest.BinaryProvider GenericForest.ScalarBits
example : (flattenAnswers xs).value=F := by rw [flatten_truth.1];simp only [badF,F,a,b];decide
