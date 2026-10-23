import Std

-- Intentionally false proposition. Production never imports this file.
-- An unsound packing-tightness checker must reject it.
example : ∃ x : Fin 3,
    (x.val = 0 ∨ x.val = 1) ∧
    (x.val = 1 ∨ x.val = 2) ∧
    (x.val = 0 ∨ x.val = 2) := by
  decide
