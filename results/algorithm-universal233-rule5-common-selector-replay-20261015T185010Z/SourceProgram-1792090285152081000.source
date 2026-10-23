import BuildIdentity
namespace OrdinaryCommonSplit.Source
open RMAF Caller
def runSource (T S : Tree) (X Y : List Nat) (p : RMAF.Vertex) (q : Nat)
    (cb : Tree→Tree→Nat→Option Forest) : Option (Option Forest) :=
  (buildSetup T S X Y p).bind fun d=>runGuarded d q cb
def sourceJobs (T S : Tree) (X Y : List Nat) (p : RMAF.Vertex) (q : Nat) : List Job :=
  match buildSetup T S X Y p with
  | none => []
  | some d => guardedJobs d q
def SourceIH (T S : Tree) (X Y : List Nat) (p : RMAF.Vertex) (q : Nat)
    (cb : Tree→Tree→Nat→Option Forest) : Prop :=
  ∀j∈sourceJobs T S X Y p q,BoundedExact j.T j.S j.budget (cb j.T j.S j.budget)

theorem source_answer_exact (T S : Tree) (X Y : List Nat) (p : RMAF.Vertex) (q : Nat)
    (cb : Tree→Tree→Nat→Option Forest) (answer : Option Forest)
    (ih : SourceIH T S X Y p q cb) (h : runSource T S X Y p q cb=some answer) :
    BoundedExact T S q answer := by
  cases hb : buildSetup T S X Y p with
  | none => simp [runSource,hb] at h
  | some d =>
    have run : runGuarded d q cb=some answer := by simpa only [runSource,hb,Option.bind_some] using h
    have ih' : GuardedIH d q cb := by simpa only [SourceIH,sourceJobs,hb,GuardedIH] using ih
    have exactness := runGuarded_answer_exact d q cb answer ih' run
    obtain ⟨ht,hs,_,_⟩ := buildSetup_identity T S X Y p d hb
    simpa only [ht,hs] using exactness

theorem source_job_progress (T S : Tree) (X Y : List Nat) (p : RMAF.Vertex) (q : Nat)
    (j : Job) (hj : j∈sourceJobs T S X Y p q) :
    Universal233.DepthOne.proper j.T j.S=true ∧ j.budget<q ∧ q-j.budget=1 := by
  cases hb : buildSetup T S X Y p with
  | none => simp [sourceJobs,hb] at hj
  | some d => exact guarded_job_progress d q j (by simpa only [sourceJobs,hb] using hj)
end OrdinaryCommonSplit.Source
