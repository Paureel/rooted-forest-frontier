import FinalWork
import FinalRecoveryControls

namespace Universal233.FinalCutRecovery.Regression
open RMAF CoreProgram Controls

def target : Tree := .node (.node (.leaf 12) (.leaf 99)) (.node (.leaf 7) (.leaf 41))
def selected : List (List Nat) := [[12,99],[7,41]]

theorem original_agreement_recovery :
    ∃ o, recover quartet selected = some o ∧ agreement target quartet o.partition = true ∧
      o.sourceCuts.length = 1 ∧ CutRealization.RealizedOutput quartet o ∧
      BlockPermutation selected o.partition := by
  obtain ⟨o,ho,ha,hc,_,hr,hperm⟩ := recover_original_agreement target quartet selected
    (by decide) (by decide)
  exact ⟨o,ho,ha,hc,hr,hperm⟩

theorem returned_original_edges :
    ([[false]] : List Vertex).Nodup ∧
      ∀ v, v ∈ ([[false]] : List Vertex) → CoreGraph.Valid quartet v ∧ v ≠ [] := by
  exact recover_edges quartet selected ⟨[[41,7],[99,12]],[[false]]⟩ (by decide)

theorem final_work_233 :
    ((meterRecover quartet selected).work : Rat) ≤ (finalPolynomial quartet selected : Rat)*(233/100 : Rat)^3 := by
  exact final_work_absorbed quartet selected (by decide) (by decide) (by decide)
    3 (by decide) (233/100) (by with_unfolding_all decide)

theorem finite_color_projection : (meterColor selected 99).value = blockColor selected 99 :=
  meterColor_value selected 99

theorem original_call_count :
    (CoreWork.meterGenerate quartet (blockColor selected) (selected.length - 1)).oracleCalls = 4 := by
  decide

end Universal233.FinalCutRecovery.Regression
