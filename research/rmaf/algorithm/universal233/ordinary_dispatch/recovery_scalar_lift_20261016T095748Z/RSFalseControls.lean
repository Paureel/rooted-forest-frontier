import RSControls
open OrdinaryDispatch.RecoveryBits OrdinaryDispatch.RecoveryScalar.Controls
example : (copiedEqual five three).value=true := by rw [copiedEqual_value];decide
example : (leBits five three).value=true := by rw [leBits_value];decide
example : decode (minBits five three).value=5 := by rw [minBits_value];decide
example : decode (subtractBits three five).value=2 := by rw [subtractBits_value];decide
example : decode (subtractBits five three).value=0 := by rw [subtractBits_value];decide
example : decode (counterInc 3 seven).value=8 := by
 rw [show decode (counterInc 3 seven).value=0 from by decide +kernel]
 decide
example : decode (counterAdd 4 three five).value=7 := by rw [counterAdd_value _ _ _ (by decide +kernel)];decide
example : (copyBits five).work=12 := by decide
example : decode (lengthBits 4 [false,true,false]).value=2 := by rw [lengthBits_value _ _ (by decide)];decide
example : decode (clipBudget 10 thousand [false,true,false]).value=1000 := by rw [clipBudget_value _ _ _ (by decide)];decide
example : decode (colorBits blocks two).value=2 := by rw [colorBits_value];decide
example : (copyGroup g7).work=48 := by decide
