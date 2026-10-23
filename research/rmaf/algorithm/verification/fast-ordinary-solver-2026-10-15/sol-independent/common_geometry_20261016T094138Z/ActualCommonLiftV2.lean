/- Both geometric obligations supplied; paid branches and refusal remain open. -/
import CoarsenGeometryV2
open RMAF ForestState Universal233 Universal233.HardParent
open Universal233.CherryBranching OrdinaryDispatch OrdinaryDispatch.FastOrdinary
namespace IndependentGeometry

theorem actual_coarsening_geometry : IndependentCommon.CoarseningGeometry := by
 intro T U reverse c hp selected F hF
 have reflection := early_sound T U
 rw [selected] at reflection
 have proper := IndependentCommon.oriented_proper_own hp reverse
 have syntactic := IndependentCommon.selected_syntax proper reflection
 have orientedAgreement : agreement (Oriented reverse T U).1 (Oriented reverse T U).2 F=true := by
  cases reverse
  · exact hF
  · exact agreement_swap hF
 have geometry := common_coarsening syntactic.1 syntactic.2 proper
  (IndependentCommon.common_fresh (Oriented reverse T U).1) F orientedAgreement
 exact ⟨_,geometry⟩

theorem actual_common_lift : IndependentReconstruction.CommonLift :=
 IndependentCommon.common_lift_from_geometry actual_expansion_geometry actual_coarsening_geometry

theorem solver_after_common_geometry
 (one : IndependentReconstruction.OneRule) (high : IndependentReconstruction.HighRule)
 (forward4 : IndependentReconstruction.ForwardRule4) (reverse4 : IndependentReconstruction.ReverseRule4)
 (hard : IndependentReconstruction.Hard2Rule) (nonrefusal : IndependentReconstruction.RejectImpossible)
 (q : Nat) : ∀T U,DepthOne.proper T U=true → QueryExact T U q (FastOrdinary.solve q T U) :=
 IndependentCommon.solver_after_common_ready actual_common_lift one high forward4 reverse4 hard nonrefusal q
end IndependentGeometry
