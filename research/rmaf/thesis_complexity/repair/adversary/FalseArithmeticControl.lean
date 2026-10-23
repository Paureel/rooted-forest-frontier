import Std
-- Deliberately false control, excluded from production proof. Expected compilation failure.
example : (4 : Int) + 2 + 3 = 8 := by decide
