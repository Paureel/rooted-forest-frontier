import Std
-- One residual component at full b does not satisfy the half-budget target.
example : (1 : Nat) ≤ 1 → 2 * 1 ≤ 1 := by decide
