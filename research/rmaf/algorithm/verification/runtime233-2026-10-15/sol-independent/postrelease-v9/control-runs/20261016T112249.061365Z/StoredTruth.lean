import StoredOrientations
open RMAF GenericForest.ScalarBits GenericForest.BinaryProvider OrdinaryDispatch.StoredNumeric
example : (maximumCopy [true] [true,false]).value=[true,false] := by decide +kernel
example : (maximumBlock [[false,false]]).value=[] := by decide +kernel
example : (freshOne (.leaf [true,true])).value=[false,false,true] := by decide +kernel
example : (freshPair (.leaf [true]) (.leaf [false])).value=([false,true],[true,true]) := by decide +kernel
example : (contractBits [false] [true] [false,true] (.node (.leaf [false]) (.leaf [true]))).value=Tree.leaf [false,true] := by decide +kernel
example : (contractBits [false] [true] [false,true] (.node (.leaf [true]) (.leaf [false]))).value=Tree.leaf [false,true] := by decide +kernel
example : stateStorageWidth 2 3 7=22 ∧ markerStorageWidth 2 3 7=24 := by decide +kernel
example : budgetStorageWidth 5 3 8=125 := by decide +kernel
example : decode (List.replicate 8 false)=0 ∧ (List.replicate 8 false).length=8 := by decide +kernel
example : (subtractBits [true,false,false] [false,true]).value=[] := by decide +kernel
