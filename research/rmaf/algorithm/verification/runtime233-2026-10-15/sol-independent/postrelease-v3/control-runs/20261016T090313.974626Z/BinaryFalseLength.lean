import PolynomialBitBound
open GenericForest.ScalarBits
example : decode (lengthBits 3 (List.range 8)).value=8 := by decide +kernel
