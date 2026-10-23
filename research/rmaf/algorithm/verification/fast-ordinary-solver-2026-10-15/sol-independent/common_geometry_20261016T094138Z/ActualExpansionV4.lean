/- Selected-program interface; four prior selector primitives remain reused. -/
import ExpansionGeometryV6
open RMAF ForestState Universal233 Universal233.HardParent
open Universal233.CherryBranching OrdinaryDispatch OrdinaryDispatch.FastOrdinary
namespace IndependentGeometry

theorem iso_sym {T U : Tree} (h : RootedIso T U) : RootedIso U T := by
 induction h with
 | leaf x => exact .leaf x
 | straight hl hr il ir => exact .straight il ir
 | swapped hl hr il ir => exact .swapped ir il

theorem agreement_swap {T U : Tree} {G : List (List Nat)} (h : agreement T U G=true) :
 agreement U T G=true := by
 simp only [agreement,Bool.and_eq_true] at h ⊢
 refine ⟨⟨⟨⟨h.1.1.1.2,h.1.1.1.1⟩,?_⟩,h.2⟩,h.1.2⟩
 apply List.all_eq_true.2
 intro B hB
 have agrees := List.all_eq_true.1 h.1.1.2 B hB
 unfold restrictionAgrees at agrees ⊢
 cases l : restrict B T <;> cases r : restrict B U <;> simp [l,r] at agrees ⊢
 exact iso_same (iso_sym (same_iso agrees))

theorem actual_expansion_geometry : IndependentCommon.ExpansionGeometry := by
 intro T U reverse c hp selected G hG
 have reflection := early_sound T U
 rw [selected] at reflection
 have proper := IndependentCommon.oriented_proper_own hp reverse
 have syntactic := IndependentCommon.selected_syntax proper reflection
 have geometry := common_expansion syntactic.1 syntactic.2 proper
   (IndependentCommon.common_fresh (Oriented reverse T U).1) G hG
 cases reverse
 · exact geometry
 · exact agreement_swap geometry

/- Exact remaining common-lift obligation, no supplied instance. -/
theorem common_lift_if_coarsening (coarsening : IndependentCommon.CoarseningGeometry) :
 IndependentReconstruction.CommonLift :=
 IndependentCommon.common_lift_from_geometry actual_expansion_geometry coarsening
end IndependentGeometry
