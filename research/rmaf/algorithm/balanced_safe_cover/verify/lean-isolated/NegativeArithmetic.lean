import Std
namespace GlobalQControls
-- Kernel-checked negation of the deliberately false exponent certificate.
theorem false_exponent_is_false :
  ¬ ((9/4 : Rat) * (1+142/100) < (19/10 : Rat)*(19/10 : Rat)) := by
  decide +kernel
-- Clean star twins alongside the false one-cut proposition.
theorem repaired_star_half : 3 - 2 ≤ 3 / 2 := by decide
theorem failed_star_half : ¬ (3 - 1 ≤ 3 / 2) := by decide
#print axioms false_exponent_is_false
#print axioms repaired_star_half
#print axioms failed_star_half
end GlobalQControls
