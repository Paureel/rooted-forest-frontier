import Std
namespace KeptParentToy
structure Cell where
  value : Nat
private theorem hidden : True := True.intro
def branch : Nat → Nat
  | 0 => 0
  | n+1 => branch n + 1
#check branch.eq_1
theorem visible : branch 0 = 0 := rfl
end KeptParentToy
