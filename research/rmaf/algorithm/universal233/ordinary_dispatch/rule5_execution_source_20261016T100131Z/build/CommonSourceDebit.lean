import CommonCallBinding
namespace Universal233.Rule5ExecutionSource
open RMAF CoreGraph HardParent Rule5PrefixLocalWork
open OrdinaryCommonSplit OrdinaryCommonSplit.Caller OrdinaryCommonSplit.Source
open OrdinaryDispatch.EarlyLocalWork OrdinaryDispatch.FullSourceWork
open WholeSourceWork CoreWork GenericForest.CheckCorrespondence
open Rule5RemainingLocalWork Rule5PendantLocalWork Rule5FinalClassification Rule5Classification Rule5Local Rule5CommonSelector

theorem run_paid_local_zero (cb : Ordinary) (W : OrdinaryWork) (d : Setup) (q : Nat) (FY FN : Forest) :
 (runPaidMeter cb W d q FY FN).localWork=(runPaidMeter cb (fun _ _ _=>0) d q FY FN).localWork := by
 simp only [runPaidMeter,jobs_answers_value,jobs_answers_local]

theorem with_outside_local_zero (cb : Ordinary) (W : OrdinaryWork) (d : Setup) (q : Nat) (FY : Forest) :
 (withOutsideMeter cb W d q FY).localWork=(withOutsideMeter cb (fun _ _ _=>0) d q FY).localWork := by
 cases h:(outsideReplyMeter d FY).value <;> simp only [withOutsideMeter,h,run_paid_local_zero]

theorem guarded_local_zero (cb : Ordinary) (W : OrdinaryWork) (d : Setup) (q : Nat) :
 (guardedMeter cb W d q).localWork=(guardedMeter cb (fun _ _ _=>0) d q).localWork := by
 cases hp:(meterPretest d.ty d.sy).value with
 | refused=>simp only [guardedMeter,hp]
 | rejected=>simp only [guardedMeter,hp]
 | found c=>cases c <;> simp only [guardedMeter,hp,with_outside_local_zero]

theorem common_local_zero (cb : Ordinary) (W : OrdinaryWork) (T S : Tree) (a b : Nat) (d : BadSelection) (q : Nat) :
 (commonMeter cb W T S a b d q).localWork=(commonMeter cb (fun _ _ _=>0) T S a b d q).localWork := by
 cases hb:(commonSetupMeter T S a b d).value <;> simp only [commonMeter,hb,guarded_local_zero]

def commonSource (cb : Ordinary) (W : OrdinaryWork) (T S : Tree) (a b : Nat) (d : BadSelection) (q : Nat) : Charged (Option Forest) :=
 let r:=commonMeter cb W T S a b d q;⟨r.value,r.localWork+r.recursiveWork⟩

theorem common_source_value (cb : Ordinary) (W : OrdinaryWork) (T S : Tree) (a b : Nat) (d : BadSelection) (q : Nat) :
 (commonSource cb W T S a b d q).value=Rule5CommonOrdinary.runSelectedCommon cb T S a b d q := common_value cb W T S a b d q

theorem map_zero_sum {α : Type} (xs : List α) : (xs.map (fun _=>0 : α→Nat)).sum=0 := by
 induction xs <;> simp_all

theorem common_source_split (cb : Ordinary) (W : OrdinaryWork) (T S : Tree) (a b : Nat) (d : BadSelection) (q : Nat) :
 (commonSource cb W T S a b d q).work=(commonSource cb (fun _ _ _=>0) T S a b d q).work+
 ((commonJobs T S a b d q).map (fun j=>W j.T j.S j.budget)).sum := by
 simp only [commonSource,common_recursive,common_calls,common_local_zero,map_zero_sum,Nat.add_zero]

theorem common_source_local (cb : Ordinary) (classFee : CheckRequest→Nat)
 {T S : Tree} {i e : RMAF.Vertex} {a b : Nat} {d : BadSelection}
 (ch : CherryAt T i a b) (ad : admitted T S a b=true)
 (sel : (finalMeter classFee T S a b).value=some (.remaining d (.one e))) (q : Nat)
 (same : ∀j,j∈commonJobs T S a b d q→cb j.T j.S j.budget=Rule5LocalWork.actual j.T j.S j.budget) :
 (commonSource cb (fun _ _ _=>0) T S a b d q).work≤commonBudget (leaves T).length (leaves S).length (subtreeLabels S d.badArc).length := by
 have bound:=common_local_on_jobs cb classFee (fun _ _ _=>0) ch ad sel q same
 have zero : (commonMeter cb (fun _ _ _=>0) T S a b d q).recursiveWork=0:=by rw [common_recursive,map_zero_sum]
 simpa only [commonSource,zero,Nat.add_zero] using bound
end Universal233.Rule5ExecutionSource
