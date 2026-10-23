import Std
namespace BlindGenerated
private def hiddenSeed : Nat := 8
inductive Token where
  | one
  | two
  deriving DecidableEq, Repr
def usesPrivate : Nat := hiddenSeed
theorem knownTrue : 2 + 2 = 4 := rfl
end BlindGenerated
