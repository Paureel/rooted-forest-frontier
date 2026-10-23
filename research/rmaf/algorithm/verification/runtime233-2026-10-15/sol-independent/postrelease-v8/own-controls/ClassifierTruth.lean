import ClassifierFeeBinding
import ClassifierFeePolynomial
open Universal233.ClassifierCheckFee
example : checkCap 0 = 3970 := by decide +kernel
example : checkCap 1 = 933634 := by decide +kernel
example : (requestMeter (.restriction (.leaf 0) (.leaf 0) [0])).value = true := by decide +kernel
example : (requestMeter (.restriction (.leaf 0) (.leaf 1) [0])).value = false := by decide +kernel
example : (requestMeter (.embedding (.leaf 0) [[0]])).value = true := by decide +kernel
example : (requestMeter (.embedding (.leaf 0) [[0],[0]])).value = false := by decide +kernel
example : (requestMeter (.restriction (.leaf 0) (.leaf 0) [0])).calls.length = 1 := by decide +kernel
