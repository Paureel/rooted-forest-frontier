import AdmittedRouteBinding
namespace Universal233.Rule5ClosedSource
open RMAF CoreGraph HardParent Rule5PrefixLocalWork Rule5ExecutionSource
open OrdinaryCommonSplit.Caller
open OrdinaryDispatch.FullSourceWork OrdinaryDispatch.WorkRecursion
open WholeSourceWork CoreWork GenericForest.CheckCorrespondence
open Rule5FinalClassification Rule5Classification Rule5Local Rule5CommonSelector

/-- Actual cutoff common jobs need checked agreement and payload bounds,
not identity with any other optimal witness returned by solve. -/
theorem actual_common_job_payload (T S : Tree) (a b : Nat) (d : BadSelection) (q : Nat)
 {j : Job} (mem:j∈commonJobs T S a b d q) {F : Forest}
 (answer:actualCallback q j.T j.S j.budget=some F) :
 agreement j.T j.S F=true ∧ Rule5LocalWork.cells F≤2*(leaves T).length ∧
 F.flatten.length≤(leaves T).length ∧ F.length≤(leaves T).length := by
 have m:j∈(commonMeter (actualCallback q) (fun _ _ _=>0) T S a b d q).calls:=by rw [common_calls];exact mem
 have progress:=common_call_progress (actualCallback q) (fun _ _ _=>0) T S a b d q m
 have size:=common_call_size (actualCallback q) (fun _ _ _=>0) T S a b d q m
 have good:=cutoff_sound q j.T j.S j.budget F progress.1 answer
 have payload:=Rule5LocalWork.agreement_payload j.T j.S F (Rule5LocalWork.proper_left_nodup progress.1) good
 exact ⟨good,by omega,by omega,by omega⟩

theorem actual_common_job_labels (T S : Tree) (a b : Nat) (d : BadSelection) (q L : Nat)
 (labels:∀x,x∈leaves T++leaves S→x<2^L) {j : Job}
 (mem:j∈commonJobs T S a b d q) {F : Forest}
 (answer:actualCallback q j.T j.S j.budget=some F) : ∀x,x∈F.flatten→x<2^(L+2) := by
 have m:j∈(commonMeter (actualCallback q) (fun _ _ _=>0) T S a b d q).calls:=by rw [common_calls];exact mem
 have progress:=common_call_progress (actualCallback q) (fun _ _ _=>0) T S a b d q m
 have bits:=common_call_bits (actualCallback q) (fun _ _ _=>0) T S a b d q L labels m
 have good:=cutoff_sound q j.T j.S j.budget F progress.1 answer
 have payload:=Rule5LocalWork.agreement_payload j.T j.S F (Rule5LocalWork.proper_left_nodup progress.1) good
 exact fun x hx=>bits.1 x (payload.2.2.1 x hx)

theorem original_input_domain (T S : Tree) (q L : Nat)
 (labels:∀x,x∈leaves T++leaves S→x<2^L) : InputDomain T S q (leaves T).length q L := by
 exact ⟨Nat.le_refl _,Nat.le_refl _,fun x hx=>labels x (by simp [hx]),fun x hx=>labels x (by simp [hx])⟩

theorem original_rule5_bound {T S : Tree} {i : RMAF.Vertex} {a b : Nat}
 (ch:CherryAt T i a b) (ad:admitted T S a b=true) (q L : Nat)
 (labels:∀x,x∈leaves T++leaves S→x<2^L) :
 ((actualRule5Source (fun _ _ _=>0) T S a b q).work:Rat)≤(C5 (leaves T).length q L:Rat)*(233/100:Rat)^q := by
 simpa only [Rule5ActualTrace.base] using actual_rule5_bound ch ad q (leaves T).length q L (original_input_domain T S q L labels)
end Universal233.Rule5ClosedSource
