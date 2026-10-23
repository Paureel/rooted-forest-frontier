import Std
set_option maxRecDepth 200000
set_option maxHeartbeats 2000000
namespace SolIndependentFalseMass
-- Deliberately false retained two-unit plus q-minus-two branching claim.
def c : Rat := 233 / 100
attribute [local reducible] Rat.add Rat.mul Rat.inv
theorem plantedFalse : 2 / c + 1 / c ^ 2 ≤ 1 := by
  unfold c
  decide +kernel
end SolIndependentFalseMass
