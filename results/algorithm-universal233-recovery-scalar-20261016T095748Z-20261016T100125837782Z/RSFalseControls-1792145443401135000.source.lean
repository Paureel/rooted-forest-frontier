import RSControls
open OrdinaryDispatch.RecoveryBits OrdinaryDispatch.RecoveryScalar.Controls
example : (copiedEqual five three).value=true := by decide
example : (leBits five three).value=true := by decide
example : (minBits five three).value=five := by decide
example : decode (subtractBits three five).value=2 := by decide
example : decode (subtractBits five three).value=0 := by decide
example : decode (counterInc 3 seven).value=8 := by decide
example : decode (counterAdd 4 three five).value=7 := by decide
example : (copyBits five).work=12 := by decide
example : decode (lengthBits 4 [false,true,false]).value=2 := by decide
example : decode (clipBudget 10 thousand [false,true,false]).value=1000 := by decide
example : (colorBits blocks two).value=two := by decide
example : (copyGroup g7).work=48 := by decide
