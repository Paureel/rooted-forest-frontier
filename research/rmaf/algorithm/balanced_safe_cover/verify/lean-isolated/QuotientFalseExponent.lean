import Std
-- Proposition-level negative control: a rational upper composed base cannot
-- be certified below 1.9 by the squared comparison.
example : (9/4 : Rat) * (1+142/100) < (19/10 : Rat) * (19/10 : Rat) := by
  decide +kernel
