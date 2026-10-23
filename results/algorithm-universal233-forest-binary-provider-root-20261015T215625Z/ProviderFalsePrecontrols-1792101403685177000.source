import ProviderPrecontrols
open GenericForest.BinaryProvider.Controls GenericForest.ScalarBits
example : (copiedEqual a paddedA).value=false := by rw [supplied_array_truth.1];decide
example : GenericForest.ScalarBits.decode a=6 := by rw [supplied_array_truth.2.1];decide
example : (copyBits a).work=0 := by rw [supplied_array_truth.2.2.2];decide
example : GenericForest.ScalarBits.decode (subtractBits [true] [false,false,true]).value=3 := by rw [supplied_counter_truth.2.1];decide
