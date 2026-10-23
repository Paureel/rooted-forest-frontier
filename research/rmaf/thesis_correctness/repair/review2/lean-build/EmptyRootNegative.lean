import Std
-- Deliberately false boundary claim. This file must fail and is never imported.
example : 3 ≤ ((1 : Nat) + 0 + 1 + 0) := by decide
