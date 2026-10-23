import Std
namespace SolIndependentFalseCycle
-- Deliberately false same-budget, unchanged-size progress proposition.
theorem plantedFalse : (5 : Nat) < 5 := by decide +kernel
end SolIndependentFalseCycle
