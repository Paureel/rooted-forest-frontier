import Rule5ArmSelectedTraceV3

namespace SourceRule5CommonJobsV3
open RMAF Universal233 SourceForestV3
open Universal233.Rule5ExecutionSource OrdinaryCommonSplit.Caller
open SourceCouplingV2 (Mode)
open SourceDisjointV2 (ordinarySpec)
variable {OrdExec : Tree→Tree→Nat→Option F→Prop} {mode : Mode}
  {base : Tree→Tree→Nat→Option F}

theorem jobs_raw_values
    (sound : ∀ T S b a,OrdExec T S b a→a=base T S b)
    (h : JobsExec OrdExec mode k js r slots) :
    r.value=js.map (fun j=>ordinarySpec mode base j.T j.S j.budget) := by
  induction h with
  | nil => rfl
  | cons head tail ih =>
    have hv:=SourceForestSingletonV2.invoke_sound head sound
    simp only [prepend,List.map_cons,hv,ih]

theorem paid_jobs_value (d : Setup) (q : Nat) : (paidJobsMeter d q).value=paidJobs d q := by
  simp only [paidJobsMeter,paidJobs]
  split <;> rfl
end SourceRule5CommonJobsV3
