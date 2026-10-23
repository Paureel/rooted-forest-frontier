import PureBridge
open PureBridge
-- Deliberately false: the two-unit repair countermodel has a one-unit repair.
example : ∃ r : Bool, r = false ∧
    Controls.badRestCost r ≤ Controls.badRestCost true + 1 := by decide
