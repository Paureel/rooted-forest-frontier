import Rule5CommonSelectedTraceV3

namespace SourceRule5PaidSelectionV3
open RMAF Universal233 WholeSourceWork SourceForestV3
open Universal233.Rule5ExecutionSource Universal233.Rule5PaidSelector
open Universal233.Rule5RemainingLocalWork Universal233.Rule5SelectedLocalWork
open SourceCouplingV2 (Mode)
open SourceDisjointV2 (ordinarySpec)
open OrdinaryDispatch.FullSourceWork CoreWork
variable {OrdExec : Tree→Tree→Nat→Option F→Prop} {mode : Mode}
  {base : Tree→Tree→Nat→Option F} {T S : Tree}

-- This is a return-value identity. The concrete eager metered execution is retained.
theorem best_raw_value (check : F→Rule5PrefixLocalWork.Measured Bool) (valid : F→Bool)
    (value : ∀ F,(check F).value=valid F) (fs : List F) :
    (bestLengthMeter check fs).value=best List.length valid fs := by
  induction fs with
  | nil => rfl
  | cons F fs ih =>
    simp only [bestLengthMeter,best,value,ih]
    cases valid F <;> cases best List.length valid fs <;> rfl

theorem accepted_raw_value (T S : Tree) (q : Nat) (F : F) :
    (originalAcceptedMeter T S q F).value=Rule5PaidOrdinary.originalAccepted T S q F := by
  simp only [originalAcceptedMeter,measuredAgreement_value,Rule5PaidOrdinary.originalAccepted]

theorem answers_raw_projection
    (sound : ∀ T S b a,OrdExec T S b a→a=base T S b)
    {R : SelectedPaid T S}
    (h : AnswersExec OrdExec mode R q k r slots) :
    r.value=(requests R.geometry q).filterMap
      (fun j=>Rule5PaidOrdinary.currentAnswer (ordinarySpec mode base) (some j.target) j.sources j.residual) ∧
    r.ordinaryCalls=(requests R.geometry q).flatMap
      (fun j=>Rule5ActualTrace.currentFrontier (ordinarySpec mode base) (some j.target) j.sources j.residual) := by
  cases h with
  | run execution =>
    have hv:=SourceRule5PaidRequestV3.list_raw_projection sound execution
    simpa only [answersReturn,requests_value] using hv

theorem best_raw_projection
    (sound : ∀ T S b a,OrdExec T S b a→a=base T S b)
    {R : SelectedPaid T S}
    (h : BestExec OrdExec mode R q k r slots) :
    r.value=Rule5ActualTrace.runPaidRequests (ordinarySpec mode base) T S q (requests R.geometry q) ∧
    r.ordinaryCalls=(requests R.geometry q).flatMap
      (fun j=>Rule5ActualTrace.currentFrontier (ordinarySpec mode base) (some j.target) j.sources j.residual) := by
  cases h with
  | run execution =>
    have hv:=answers_raw_projection sound execution
    constructor
    · simp only [bestReturn,best_raw_value _ _ (accepted_raw_value T S q),hv.1,Rule5ActualTrace.runPaidRequests]
    · exact hv.2

end SourceRule5PaidSelectionV3
