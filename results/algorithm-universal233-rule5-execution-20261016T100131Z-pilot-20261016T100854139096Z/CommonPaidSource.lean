import CommonOutsideSource
namespace Universal233.Rule5ExecutionSource
open RMAF CoreGraph Rule5PrefixLocalWork
open OrdinaryCommonSplit OrdinaryCommonSplit.Caller OrdinaryCommonSplit.Source
open OrdinaryDispatch.EarlyLocalWork OrdinaryDispatch.FullSourceWork
open WholeSourceWork CoreWork GenericForest.CheckCorrespondence
abbrev Forest:=List (List Nat)
abbrev Ordinary:=Tree→Tree→Nat→Option Forest
abbrev OrdinaryWork:=Tree→Tree→Nat→Nat

structure CommonReceipt (α : Type) where
 value : α
 localWork : Nat
 recursiveWork : Nat
 calls : List Job

/-- Both list entries compute their residual independently in the source. -/
def paidJobsMeter (d : Setup) (q : Nat) : Charged (List Job) :=
 if q=0 then ⟨[],2⟩ else ⟨[⟨d.tx,d.sx,q-1⟩,⟨d.mxT,d.mxS,q-1⟩],12⟩

theorem paid_jobs_value (d : Setup) (q : Nat) : (paidJobsMeter d q).value=paidJobs d q := by
 unfold paidJobsMeter paidJobs;split <;> rfl

theorem paid_jobs_work (d : Setup) (q : Nat) : (paidJobsMeter d q).work≤12 := by
 unfold paidJobsMeter;split <;> dsimp only <;> omega

def jobsAnswersMeter (cb : Ordinary) (W : OrdinaryWork) : List Job→CommonReceipt (List (Option Forest))
 | []=>⟨[],1,0,[]⟩
 | j::js=>let a:=cb j.T j.S j.budget;let r:=jobsAnswersMeter cb W js
           ⟨a::r.value,r.localWork+3,W j.T j.S j.budget+r.recursiveWork,j::r.calls⟩

theorem jobs_answers_value (cb : Ordinary) (W : OrdinaryWork) (js : List Job) :
 (jobsAnswersMeter cb W js).value=js.map (fun j=>cb j.T j.S j.budget) := by
 induction js <;> simp_all [jobsAnswersMeter]

theorem jobs_answers_local (cb : Ordinary) (W : OrdinaryWork) (js : List Job) :
 (jobsAnswersMeter cb W js).localWork=3*js.length+1 := by
 induction js <;> simp_all [jobsAnswersMeter] <;> omega

theorem jobs_answers_calls (cb : Ordinary) (W : OrdinaryWork) (js : List Job) :
 (jobsAnswersMeter cb W js).calls=js := by induction js <;> simp_all [jobsAnswersMeter]

theorem jobs_answers_recursive (cb : Ordinary) (W : OrdinaryWork) (js : List Job) :
 (jobsAnswersMeter cb W js).recursiveWork=(js.map (fun j=>W j.T j.S j.budget)).sum := by
 induction js <;> simp_all [jobsAnswersMeter]

/-- The strict map is completed before the two-answer match. In particular a
failed first callback does not remove the second paid callback occurrence. -/
def runPaidMeter (cb : Ordinary) (W : OrdinaryWork) (d : Setup) (q : Nat) (FY FN : Forest) : CommonReceipt (Option Forest) :=
 let js:=paidJobsMeter d q;let asw:=jobsAnswersMeter cb W js.value
 let finish : Charged (Option Forest):=
  match asw.value with
  | [some FX,some FM]=>
    let r:=Rule5LocalWork.reconstructMeter (measuredAgreement d.T d.S) d FX FY FM FN
    match r.value with
    | none=>⟨none,r.work+2⟩
    | some G=>⟨if G.length-1≤q then some G else none,r.work+G.length+4⟩
  | _=>⟨none,2⟩
 ⟨finish.value,js.work+asw.localWork+finish.work+2,asw.recursiveWork,asw.calls⟩

theorem run_paid_value (cb : Ordinary) (W : OrdinaryWork) (d : Setup) (q : Nat) (FY FN : Forest) :
 (runPaidMeter cb W d q FY FN).value=runPaid d q FY FN cb := by
 simp only [runPaidMeter,paid_jobs_value,jobs_answers_value,runPaid,reconstruct_actual_agreement]
 split
 · split <;> simp_all
 · split <;> simp_all

theorem run_paid_calls (cb : Ordinary) (W : OrdinaryWork) (d : Setup) (q : Nat) (FY FN : Forest) :
 (runPaidMeter cb W d q FY FN).calls=paidJobs d q := by
 simp only [runPaidMeter,jobs_answers_calls,paid_jobs_value]

theorem run_paid_recursive (cb : Ordinary) (W : OrdinaryWork) (d : Setup) (q : Nat) (FY FN : Forest) :
 (runPaidMeter cb W d q FY FN).recursiveWork=
 (((runPaidMeter cb W d q FY FN).calls).map (fun j=>W j.T j.S j.budget)).sum := by
 simp only [runPaidMeter,jobs_answers_calls,jobs_answers_recursive]
end Universal233.Rule5ExecutionSource
