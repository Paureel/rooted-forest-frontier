import Std
-- Deliberately false recurrence control. Compilation MUST fail.
example : (9:Nat) ≤ 8 := by decide
