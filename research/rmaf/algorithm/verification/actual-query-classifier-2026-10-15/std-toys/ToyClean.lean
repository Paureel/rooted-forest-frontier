import Std
namespace QueryClassifierToyClean
private def literalProbe : Nat := 3
structure Trace where
  slot : Nat
  budget : Nat
  deriving DecidableEq, Repr

def paidBudget (q known p : Nat) := q-known-2*(p-1)
def chooseRaw (q : Nat) (probe full : List Nat) :=
  if q<literalProbe then [] else if probe.isEmpty then full else probe

theorem two_slots : paidBudget 5 0 2 = 3 := by decide
theorem sole_slot : paidBudget 5 0 1 = 5 := by decide
theorem literal_probe : literalProbe = 3 := rfl
theorem reuse_multiplicity : chooseRaw 4 [7,7] [9] = [7,7] := by decide
theorem below_three_no_output : chooseRaw 2 [7] [9] = [] := by decide
#print axioms two_slots
#print axioms sole_slot
#print axioms reuse_multiplicity
end QueryClassifierToyClean
