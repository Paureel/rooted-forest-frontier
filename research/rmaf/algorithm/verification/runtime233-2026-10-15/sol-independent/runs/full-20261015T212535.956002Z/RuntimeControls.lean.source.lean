import Std

/- One-shot precontact runtime/counting calibration. These hand-specified controls
   make no assertion about an unreleased algorithm or its source. -/
set_option maxRecDepth 200000
set_option maxHeartbeats 2000000
namespace SolIndependentControls

def c : Rat := 233 / 100
def retainedMass : Rat := 2 / c + 1 / c ^ 2
def gamma : Rat := 2 / c + 4 / c ^ 4
def natWork : Nat → Nat
  | 0 => 1
  | n + 1 => 2 * natWork n + 3

theorem literalTrace : (5 + 3 + 2 + 7 + 11 + 13 : Nat) = 41 := by decide
theorem literalDuplicateFailure : (5 + 3 + 7 + 2 + 7 + 2 + 11 : Nat) = 37 := by decide
theorem retainedMassReject : retainedMass = (56600 : Rat) / 54289 ∧ 1 < retainedMass := by
  unfold retainedMass c
  decide
theorem gammaExact : gamma = (2929867400 : Rat) / 2947295521 := by
  unfold gamma c
  decide
theorem gammaRange : 0 < gamma ∧ gamma < 1 := by
  unfold gamma c
  decide
theorem sameBudgetStrictSize : (4 : Nat) < 5 := by decide
theorem oneCoefficientFrontier : (7 * 2929867400 : Nat) ≤ 7 * 2947295521 := by decide
theorem twoCoefficientFrontiersFail : ¬ ((2 * 7 * 2929867400 : Nat) ≤ 7 * 2947295521) := by decide
theorem emptyForestDirect : (2 + 17 : Nat) = 19 := by decide
theorem completeSourceSheet : (3 + 5 + 7 + 11 + 13 + 17 : Nat) = 56 := by decide
theorem tinyRecursiveWork : natWork 2 = 13 := by decide
theorem nullWork : ([] : List Nat).sum = 0 := by decide

#print axioms literalTrace
#print axioms literalDuplicateFailure
#print axioms retainedMassReject
#print axioms gammaExact
#print axioms gammaRange
#print axioms sameBudgetStrictSize
#print axioms oneCoefficientFrontier
#print axioms twoCoefficientFrontiersFail
#print axioms emptyForestDirect
#print axioms completeSourceSheet
#print axioms tinyRecursiveWork
#print axioms nullWork
end SolIndependentControls
