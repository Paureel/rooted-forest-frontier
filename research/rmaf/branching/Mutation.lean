import Std
-- Deliberately false arithmetic plant; compiler rejection is required.
theorem corrupted_macro_a : 2 * 231^3 * 100 + 30 * 100^4 ≤ 231^4 := by decide
