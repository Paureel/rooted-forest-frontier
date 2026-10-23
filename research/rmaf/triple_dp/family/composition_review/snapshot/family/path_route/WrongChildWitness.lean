import Std
/- One-shot negative control: deliberately false proposition, must not compile. -/
def incursionSupport : List (List Bool) := [[], [false], [false, false], [true]]
example : [true] ∈ incursionSupport →
    ([true, false] ∈ incursionSupport ∨ [true, true] ∈ incursionSupport) := by
  decide
