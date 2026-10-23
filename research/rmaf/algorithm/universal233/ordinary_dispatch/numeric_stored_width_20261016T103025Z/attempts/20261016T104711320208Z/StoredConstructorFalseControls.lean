import StoredControls
open OrdinaryDispatch.StoredNumeric OrdinaryDispatch.StoredNumeric.Controls GenericForest.ScalarBits GenericForest.BinaryProvider
example : (freshOne (.leaf [true,false,false,false])).value.length≤2 := by cbv
example : decode (freshOne (.leaf [true,true,true])).value=0 := by rw [freshOne_value];decide
example : (maximumCopy [] padded).work=0 := by cbv
example : padded.length≤0 := by decide
