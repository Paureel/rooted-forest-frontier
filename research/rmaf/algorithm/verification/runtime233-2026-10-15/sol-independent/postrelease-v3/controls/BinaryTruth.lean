import PolynomialBitBound
open RMAF GenericForest.ScalarBits Universal233.WholeSourceWork
set_option maxRecDepth 100000
example : (compareBits [true] [true,false,false]).value=Order.equal ∧ (compareBits [true] [true,false,false]).work=26 := by decide +kernel
example : (copiedEqual [true] [true,false,false]).value=true ∧ (copiedEqual [true] [true,false,false]).work=50 := by decide +kernel
example : decode (addCarry false [true,true,true] [true]).value=8 ∧ (addCarry false [true,true,true] [true]).work=40 := by decide +kernel
example : decode (subtractBits [false,false,false,true] [true]).value=7 ∧ (subtractBits [false,false,false,true] [true]).work=90 := by decide +kernel
example : decode (subtractBits [true] [false,true]).value=0 := by decide +kernel
example : decode (encode 3 7)=7 ∧ decode (encode 3 8)=0 := by decide +kernel
example : decode (lengthBits 3 (List.range 7)).value=7 ∧ (lengthBits 3 (List.range 7)).work=436 ∧ decode (lengthBits 3 (List.range 8)).value=0 := by decide +kernel
example : (indexBits 3 [0,1,2] [false,true,false]).value=some 2 ∧ (indexBits 3 [0,1,2] [false,true,false]).work=236 := by decide +kernel
example : (indexBits 3 [0,1,2] [true,true,false]).value=none ∧ (indexBits 3 [0,1,2] [true,true,false]).work=310 := by decide +kernel
example : (referenceEq 1 0 2).value=true := by decide +kernel
example : binaryInspectionPolynomial 2 1 0=16384000000000 := by decide +kernel
