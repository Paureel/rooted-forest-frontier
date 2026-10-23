import ScalarControls
open RMAF ForestState Universal233 WholeSourceWork GenericForest.CheckCorrespondence GenericForest.ScalarBits GenericForest.ScalarBits.Controls
example : (equalBits [true] [true,false,false]).value=false := by rw [comparisons.1];decide
example : GenericForest.ScalarBits.decode (addBits [true,true,true,true,true] [true]).value=0 := by rw [carry_borrow.1];decide
example : GenericForest.ScalarBits.decode (subtractBits [true] [false,false,false,false,false,true]).value=31 := by rw [carry_borrow.2.2];decide
example : (indexBits 4 [8,9,10] [true,true]).value=some 10 := by rw [binary_counters.2.2];decide
example : (referenceEq 4 0 0).work=0 := by rw [binary_checks_charged.2.1];decide
example : (bitChecked 4 (some leaf) [leaf] 0 [[0],[0]]).value=some [[0],[0]] := by rw [binary_checks.2.2];decide
