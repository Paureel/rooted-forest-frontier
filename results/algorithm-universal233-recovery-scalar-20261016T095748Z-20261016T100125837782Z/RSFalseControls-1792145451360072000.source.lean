import RSControls
open OrdinaryDispatch.RecoveryBits OrdinaryDispatch.RecoveryScalar.Controls
example : (copiedEqual five three).value=true := by decide +kernel
example : (leBits five three).value=true := by decide +kernel
example : (minBits five three).value=five := by decide +kernel
example : decode (subtractBits three five).value=2 := by decide +kernel
example : decode (subtractBits five three).value=0 := by decide +kernel
example : decode (counterInc 3 seven).value=8 := by decide +kernel
example : decode (counterAdd 4 three five).value=7 := by decide +kernel
example : (copyBits five).work=12 := by decide +kernel
example : decode (lengthBits 4 [false,true,false]).value=2 := by decide +kernel
example : decode (clipBudget 10 thousand [false,true,false]).value=1000 := by decide +kernel
example : (colorBits blocks two).value=two := by decide +kernel
example : (copyGroup g7).work=48 := by decide +kernel
