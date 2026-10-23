import Std
namespace CallerGenerated
private def hiddenSeed : Nat := 8
inductive Token where
 | leaf : Nat → Token
 | fork : Token → Token → Token
 deriving DecidableEq, Repr
def usesPrivate : Nat := hiddenSeed
theorem knownTrue : 3 + 4 = 7 := rfl
end CallerGenerated
