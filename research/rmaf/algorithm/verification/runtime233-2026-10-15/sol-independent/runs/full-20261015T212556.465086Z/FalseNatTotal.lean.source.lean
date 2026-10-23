import Std
namespace SolIndependentFalseNat
-- Deliberately false work of a fully specified tiny recursive cost function.
def natWork : Nat → Nat
  | 0 => 1
  | n + 1 => 2 * natWork n + 3
theorem plantedFalse : natWork 2 = 12 := by decide +kernel
end SolIndependentFalseNat
