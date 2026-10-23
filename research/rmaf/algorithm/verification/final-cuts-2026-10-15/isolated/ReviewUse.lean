import FinalWork
namespace IndependentFinalCutUse
open RMAF Universal233.CoreProgram Universal233.FinalCutRecovery
def source : Tree := .node (.node (.leaf 0) (.node (.leaf 1) (.leaf 2))) (.node (.leaf 3) (.leaf 4))
def target : Tree := .node (.node (.leaf 4) (.leaf 3)) (.node (.node (.leaf 2) (.leaf 1)) (.leaf 0))
def partition : List (List Nat) := [[4,3],[2,0],[1]]
theorem original_AF_consumer :
 ∃ o, recover source partition = some o ∧ agreement target source o.partition = true ∧
 o.sourceCuts.length = 2 ∧ Universal233.CutRealization.RealizedOutput source o ∧
 BlockPermutation partition o.partition := by
 obtain ⟨o,ho,ha,hc,_,hr,hperm⟩ := recover_original_agreement target source partition (by decide) (by decide)
 exact ⟨o,ho,ha,by simpa [partition] using hc,hr,hperm⟩
theorem once_only_233_consumer :
 ((meterRecover source partition).work : Rat) ≤ (finalPolynomial source partition : Rat)*(233/100 : Rat)^3 := by
 exact final_work_absorbed source partition (by decide) (by decide) (by decide) 3 (by decide) (233/100) (by with_unfolding_all decide)
def quartet : Tree := .node (.node (.leaf 0) (.leaf 1)) (.node (.leaf 2) (.leaf 3))
def crossed : Tree := .node (.node (.leaf 0) (.leaf 2)) (.node (.leaf 1) (.leaf 3))
theorem source_success_does_not_infer_target :
 inputCheck quartet [[0,1],[2,3]] = true ∧ agreement crossed quartet [[0,1],[2,3]] = false ∧
 ((recover quartet [[0,1],[2,3]]).map (fun o => agreement crossed quartet o.partition)) = some false := by decide
end IndependentFinalCutUse
#print axioms IndependentFinalCutUse.original_AF_consumer
#print axioms IndependentFinalCutUse.once_only_233_consumer
#print axioms IndependentFinalCutUse.source_success_does_not_infer_target
