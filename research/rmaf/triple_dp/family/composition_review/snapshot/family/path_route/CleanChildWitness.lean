import Std
/- One-shot clean twin: exact negation of the false control. -/
def incursionSupport : List (List Bool) := [[], [false], [false, false], [true]]
theorem leafless_incursion_exists : ¬ ([true] ∈ incursionSupport →
    ([true, false] ∈ incursionSupport ∨ [true, true] ∈ incursionSupport)) := by
  decide
#print axioms leafless_incursion_exists
