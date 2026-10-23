import Std
/- Intentional negative control. Required outcome: compiler rejection. -/
theorem falseUniformChainMass :
    2 * 100 * 231^3 + 4 * 100^4 < 231^4 := by decide
