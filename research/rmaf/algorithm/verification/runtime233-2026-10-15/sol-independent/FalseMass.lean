import Std
import Init.Data.Rat.Lemmas
set_option maxRecDepth 200000
set_option maxHeartbeats 2000000
namespace SolIndependentFalseMass
-- Deliberately false retained two-unit plus q-minus-two branching claim.
def c : Rat := 233 / 100
theorem plantedFalse : 2 / c + 1 / c ^ 2 ≤ 1 := by
  have hm : 2 / c + 1 / c ^ 2 = (56600 : Rat) / 54289 := by decide +kernel
  have hn : ((56600 : Rat) / 54289).num = 56600 := by decide +kernel
  have hd : ((56600 : Rat) / 54289).den = 54289 := by decide +kernel
  rw [hm, Rat.le_iff, hn, hd]
  decide +kernel
end SolIndependentFalseMass
