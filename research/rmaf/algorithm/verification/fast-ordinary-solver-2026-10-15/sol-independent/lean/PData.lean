/- Additional representation calibration: full constructor/recursor data. -/
namespace PrecontactData
inductive Toy where
  | base : Toy
  | step : Nat → Toy → Toy
def value : Toy := .step 9 .base
def drop : Toy → Toy
  | .base => .base
  | .step _ child => child
theorem dropValue : drop value = .base := rfl
end PrecontactData
