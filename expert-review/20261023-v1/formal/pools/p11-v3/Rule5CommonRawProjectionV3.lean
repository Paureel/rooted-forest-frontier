import Rule5CommonRawJobsV3

namespace SourceRule5CommonV3
open RMAF Universal233 WholeSourceWork SourceForestV3
open Universal233.Rule5ExecutionSource Universal233.Rule5RemainingLocalWork
open OrdinaryCommonSplit.Caller GenericForest.CheckCorrespondence
open OrdinaryDispatch.EarlyLocalWork OrdinaryDispatch.FullSourceWork
open SourceCouplingV2 (Mode)
open SourceDisjointV2 (ordinarySpec)
variable {OrdExec : Tree→Tree→Nat→Option F→Prop} {mode : Mode}
  {base : Tree→Tree→Nat→Option F} {T S : Tree}

theorem reconstruction_raw_value (d : Setup) (q : Nat) (FY FN : F) (ans : List (Option F)) :
    (reconstruction d q FY FN ans).value=Rule5ActualTrace.finishPaid d q FY FN ans := by
  have recVal : ∀ FX FM,
      (Rule5LocalWork.reconstructMeter (measuredAgreement d.T d.S) d FX FY FM FN).value=
        reconstruct d FX FY FM FN := by
    intro FX FM
    exact Rule5LocalWork.reconstruct_value _ _ _ _ _ _ (by
      intro G membership
      exact OrdinaryDispatch.FullSourceWork.measuredAgreement_value _ _ _)
  cases ans with
  | nil => rfl
  | cons x xs =>
    cases xs with
    | nil => cases x <;> rfl
    | cons y ys =>
      cases ys with
      | cons z zs => cases x <;> cases y <;> rfl
      | nil =>
        cases x with
        | none => cases y <;> rfl
        | some FX =>
          cases y with
          | none => rfl
          | some FM =>
            cases he:reconstruct d FX FY FM FN <;>
              simp only [reconstruction,Rule5ActualTrace.finishPaid,recVal,he]

theorem paid_raw_projection
    (sound : ∀ T S b a,OrdExec T S b a→a=base T S b)
    (h : PaidExec OrdExec mode d q k FY FN r slots) :
    r.value=Rule5ActualTrace.finishPaid d q FY FN
        ((paidJobs d q).map (fun j=>ordinarySpec mode base j.T j.S j.budget)) ∧
    r.calls=paidJobs d q := by
  cases h with
  | run jobs =>
    have hv:=SourceRule5CommonJobsV3.jobs_raw_values sound jobs
    have hc:=SourceRule5CommonJobsV3.jobs_calls jobs
    constructor
    · simp only [paidReturn,reconstruction_raw_value,hv,SourceRule5CommonJobsV3.paid_jobs_value]
    · simp only [paidReturn,hc,SourceRule5CommonJobsV3.paid_jobs_value]

theorem common_raw_projection
    (sound : ∀ T S b a,OrdExec T S b a→a=base T S b)
    (h : CommonExec OrdExec mode T S a b q k d r slots) :
    r.value=(Rule5ActualTrace.commonTrace (ordinarySpec mode base) T S a b d q).value.join ∧
    r.calls=(Rule5ActualTrace.commonTrace (ordinarySpec mode base) T S a b d q).calls := by
  cases h with
  | refused empty =>
    rw [Universal233.Rule5RemainingLocalWork.common_setup_value] at empty
    simp only [Rule5ActualTrace.commonTrace,empty,Option.join_none]
    constructor <;> first | rfl | trivial
  | @built setup rr slots found execution =>
    rw [Universal233.Rule5RemainingLocalWork.common_setup_value] at found
    cases execution with
    | refused empty =>
      cases hp:DepthOne.pretest01 setup.ty setup.sy with
      | refused => simp only [commonReturn,Rule5ActualTrace.commonTrace,found,hp,Option.join_none];constructor <;> first | rfl | trivial
      | rejected => simp only [commonReturn,Rule5ActualTrace.commonTrace,found,hp,Option.join_none];constructor <;> first | rfl | trivial
      | found pair =>
        cases pair with
        | none => simp only [commonReturn,Rule5ActualTrace.commonTrace,found,hp,Option.join_none];constructor <;> first | rfl | trivial
        | some p =>
          exact False.elim (empty ⟨p,by rw [OrdinaryDispatch.EarlyLocalWork.meterPretest_value];exact hp⟩)
    | @found p rr slots selected outside =>
      rw [OrdinaryDispatch.EarlyLocalWork.meterPretest_value] at selected
      cases outside with
      | refused empty =>
        rw [Universal233.Rule5ExecutionSource.outside_reply_value,OrdinaryDispatch.EarlyLocalWork.meterForest_value] at empty
        simp only [commonReturn,guardedReturn,Rule5ActualTrace.commonTrace,found,selected,empty,Option.join_some]
        constructor <;> first | rfl | trivial
      | paid outFound paid =>
        have hp:=paid_raw_projection sound paid
        rw [Universal233.Rule5ExecutionSource.outside_reply_value,OrdinaryDispatch.EarlyLocalWork.meterForest_value] at outFound
        simp only [OrdinaryDispatch.EarlyLocalWork.meterForest_value] at hp
        simp only [commonReturn,guardedReturn,outsideReturn,Rule5ActualTrace.commonTrace,found,selected,outFound,Option.join_some]
        exact hp

theorem common_actual_trace
    (sound : ∀ T S b a,OrdExec T S b a→a=base T S b)
    (h : CommonExec OrdExec mode T S a b q k d r slots) :
    r.value=(Rule5ActualTrace.commonTrace (ordinarySpec mode base) T S a b d q).value.join ∧
    slots.map (fun s=>(s.index,s.query))=CallbackPairingAuthor.indexFrom k
      (Rule5ActualTrace.directQueries (Rule5ActualTrace.commonTrace (ordinarySpec mode base) T S a b d q).calls) := by
  have hv:=common_raw_projection sound h
  refine ⟨hv.1,?_⟩
  have hi:=common_index h
  simpa only [queries,hv.2,Rule5ActualTrace.directQueries] using hi
end SourceRule5CommonV3
