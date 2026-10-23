import CommonExecutionBinding
namespace Universal233.Rule5ExecutionSource
open RMAF CoreGraph HardParent Rule5PrefixLocalWork
open OrdinaryCommonSplit OrdinaryCommonSplit.Caller OrdinaryCommonSplit.Source
open OrdinaryDispatch.EarlyLocalWork OrdinaryDispatch.FullSourceWork
open WholeSourceWork CoreWork GenericForest.CheckCorrespondence
open Rule5RemainingLocalWork Rule5PendantLocalWork Rule5FinalClassification Rule5Classification Rule5Local Rule5CommonSelector

theorem jobs_answers_congr (cb cb' : Ordinary) (W : OrdinaryWork) (js : List Job)
 (same : ∀j,j∈js→cb j.T j.S j.budget=cb' j.T j.S j.budget) :
 jobsAnswersMeter cb W js=jobsAnswersMeter cb' W js := by
 induction js with
 | nil=>rfl
 | cons j js ih=>
  have a:=same j (by simp);have r:=ih (fun k hk=>same k (by simp [hk]))
  simp only [jobsAnswersMeter,a,r]

theorem run_paid_congr (cb cb' : Ordinary) (W : OrdinaryWork) (d : Setup) (q : Nat) (FY FN : Forest)
 (same : ∀j,j∈paidJobs d q→cb j.T j.S j.budget=cb' j.T j.S j.budget) :
 runPaidMeter cb W d q FY FN=runPaidMeter cb' W d q FY FN := by
 have h:=jobs_answers_congr cb cb' W (paidJobsMeter d q).value (by simpa only [paid_jobs_value] using same)
 simp only [runPaidMeter,h]

theorem with_outside_congr (cb cb' : Ordinary) (W : OrdinaryWork) (d : Setup) (q : Nat) (FY : Forest)
 (same : ∀j,j∈paidJobs d q→cb j.T j.S j.budget=cb' j.T j.S j.budget) :
 withOutsideMeter cb W d q FY=withOutsideMeter cb' W d q FY := by
 unfold withOutsideMeter
 cases h:(outsideReplyMeter d FY).value with
 | none=>simp only [h]
 | some FN=>simp only [h,run_paid_congr cb cb' W d q FY FN same]

theorem guarded_congr (cb cb' : Ordinary) (W : OrdinaryWork) (d : Setup) (q : Nat)
 (same : ∀j,j∈guardedJobs d q→cb j.T j.S j.budget=cb' j.T j.S j.budget) :
 guardedMeter cb W d q=guardedMeter cb' W d q := by
 simp only [guardedMeter]
 split
 · rename_i p hp
   have native : DepthOne.pretest01 d.ty d.sy=.found (some p):=by simpa only [meterPretest_value] using hp
   have paid : ∀j,j∈paidJobs d q→cb j.T j.S j.budget=cb' j.T j.S j.budget := by
    simpa only [guardedJobs,native] using same
   rw [with_outside_congr cb cb' W d q _ paid]
 · rfl

theorem common_congr_on_jobs (cb cb' : Ordinary) (W : OrdinaryWork) (T S : Tree) (a b : Nat) (d : BadSelection) (q : Nat)
 (same : ∀j,j∈commonJobs T S a b d q→cb j.T j.S j.budget=cb' j.T j.S j.budget) :
 commonMeter cb W T S a b d q=commonMeter cb' W T S a b d q := by
 simp only [commonMeter]
 split
 · rfl
 · rename_i built hb
   have native : buildSetup T S (subtreeLabels S d.badArc) (outsideLabels S a b d) d.badArc=some built := by
    simpa only [common_setup_value] using hb
   have same' : ∀j,j∈guardedJobs built q→cb j.T j.S j.budget=cb' j.T j.S j.budget := by
    simpa only [commonJobs,sourceJobs,native] using same
   rw [guarded_congr cb cb' W built q same']

/-- Callers need equality with the closed ordinary solver only at the actual
listed common jobs. This consumes no global whole-cost premise. -/
theorem common_local_on_jobs (cb : Ordinary) (classFee : CheckRequest→Nat) (W : OrdinaryWork)
 {T S : Tree} {i e : RMAF.Vertex} {a b : Nat} {d : BadSelection}
 (ch : CherryAt T i a b) (ad : admitted T S a b=true)
 (sel : (finalMeter classFee T S a b).value=some (.remaining d (.one e))) (q : Nat)
 (same : ∀j,j∈commonJobs T S a b d q→cb j.T j.S j.budget=Rule5LocalWork.actual j.T j.S j.budget) :
 (commonMeter cb W T S a b d q).localWork≤commonBudget (leaves T).length (leaves S).length (subtreeLabels S d.badArc).length := by
 rw [common_congr_on_jobs cb Rule5LocalWork.actual W T S a b d q same]
 exact common_local classFee W ch ad sel q

theorem common_call_size (cb : Ordinary) (W : OrdinaryWork) (T S : Tree) (a b : Nat) (d : BadSelection) (q : Nat)
 {j : Job} (mem : j∈(commonMeter cb W T S a b d q).calls) :
 (leaves j.T).length≤(leaves T).length ∧ (leaves j.S).length≤(leaves S).length := by
 have native : j∈(Rule5ActualTrace.commonTrace cb T S a b d q).calls := by
  rw [Rule5ActualTrace.common_calls]
  rwa [common_calls] at mem
 exact Rule5ActualTrace.common_job_size cb T S a b d q native
end Universal233.Rule5ExecutionSource
