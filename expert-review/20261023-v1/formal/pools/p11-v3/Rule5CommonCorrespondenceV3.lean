import Rule5CommonExecutionV3

namespace SourceRule5CommonV3
open RMAF Universal233 WholeSourceWork SourceForestV3
open Universal233.Rule5ExecutionSource Universal233.Rule5RemainingLocalWork
open OrdinaryCommonSplit.Caller GenericForest.CheckCorrespondence
open OrdinaryDispatch.EarlyLocalWork
open SourceCouplingV2 (Mode enabled)

variable {OrdExec : Tree→Tree→Nat→Option F→Prop} {mode : Mode} {T S : Tree}

def queries (calls : List Job) := calls.map (fun j=>((j.T,j.S),j.budget))

theorem paid_index (h : PaidExec OrdExec mode d q k FY FN r slots) :
    slots.map (fun s=>(s.index,s.query))=CallbackPairingAuthor.indexFrom k (queries r.calls) := by
  cases h with
  | run jobs =>
    have hc:=SourceRule5CommonJobsV3.jobs_calls jobs
    have hi:=SourceRule5CommonJobsV3.jobs_index jobs
    simpa only [paidReturn,queries,hc] using hi

theorem outside_index (h : OutsideExec OrdExec mode d q k FY r slots) :
    slots.map (fun s=>(s.index,s.query))=CallbackPairingAuthor.indexFrom k (queries r.calls) := by
  cases h with
  | refused empty => rfl
  | paid found execution =>
    have hi:=paid_index execution
    simpa only [outsideReturn] using hi

theorem guarded_index (h : GuardedExec OrdExec mode d q k r slots) :
    slots.map (fun s=>(s.index,s.query))=CallbackPairingAuthor.indexFrom k (queries r.calls) := by
  cases h with
  | refused empty => rfl
  | found selected execution =>
    have hi:=outside_index execution
    simpa only [guardedReturn] using hi

theorem common_index (h : CommonExec OrdExec mode T S a b q k d r slots) :
    slots.map (fun s=>(s.index,s.query))=CallbackPairingAuthor.indexFrom k (queries r.calls) := by
  cases h with
  | refused empty => rfl
  | built found execution =>
    have hi:=guarded_index execution
    simpa only [commonReturn] using hi

theorem paid_slots_realize (h : PaidExec OrdExec mode d q k FY FN r slots) :
    ∀ s∈slots,SlotRealizes OrdExec mode s := by
  cases h with
  | run jobs => exact SourceRule5CommonJobsV3.jobs_slots_realize jobs

theorem outside_slots_realize (h : OutsideExec OrdExec mode d q k FY r slots) :
    ∀ s∈slots,SlotRealizes OrdExec mode s := by
  cases h with
  | refused empty => simp
  | paid found execution => exact paid_slots_realize execution

theorem guarded_slots_realize (h : GuardedExec OrdExec mode d q k r slots) :
    ∀ s∈slots,SlotRealizes OrdExec mode s := by
  cases h with
  | refused empty => simp
  | found selected execution => exact outside_slots_realize execution

theorem common_slots_realize (h : CommonExec OrdExec mode T S a b q k d r slots) :
    ∀ s∈slots,SlotRealizes OrdExec mode s := by
  cases h with
  | refused empty => simp
  | built found execution => exact guarded_slots_realize execution

theorem paid_exists
    (total : ∀ T S b,enabled mode b=true→∃ a,OrdExec T S b a)
    (d : Setup) (q k : Nat) (FY FN : F) : ∃ r slots,PaidExec OrdExec mode d q k FY FN r slots := by
  obtain ⟨r,slots,jobs⟩:=SourceRule5CommonJobsV3.jobs_exists total (paidJobsMeter d q).value k
  exact ⟨_,_,PaidExec.run jobs⟩

theorem outside_exists
    (total : ∀ T S b,enabled mode b=true→∃ a,OrdExec T S b a)
    (d : Setup) (q k : Nat) (FY : F) : ∃ r slots,OutsideExec OrdExec mode d q k FY r slots := by
  cases he:(outsideReplyMeter d FY).value with
  | none => exact ⟨_,_,OutsideExec.refused he⟩
  | some FN =>
    obtain ⟨r,slots,execution⟩:=paid_exists total d q k FY FN
    exact ⟨_,_,OutsideExec.paid he execution⟩

theorem guarded_exists
    (total : ∀ T S b,enabled mode b=true→∃ a,OrdExec T S b a)
    (d : Setup) (q k : Nat) : ∃ r slots,GuardedExec OrdExec mode d q k r slots := by
  by_cases found:∃ p,(meterPretest d.ty d.sy).value=.found (some p)
  · obtain ⟨p,hp⟩:=found
    obtain ⟨r,slots,execution⟩:=outside_exists total d q k (meterForest d.sy (some p)).value
    exact ⟨_,_,GuardedExec.found hp execution⟩
  · exact ⟨_,_,GuardedExec.refused found⟩

theorem common_exists
    (total : ∀ T S b,enabled mode b=true→∃ a,OrdExec T S b a)
    (T S : Tree) (a b q k : Nat) (d : Rule5FinalClassification.BadSelection) :
    ∃ r slots,CommonExec OrdExec mode T S a b q k d r slots := by
  cases he:(commonSetupMeter T S a b d).value with
  | none => exact ⟨_,_,CommonExec.refused he⟩
  | some setup =>
    obtain ⟨r,slots,execution⟩:=guarded_exists total setup q k
    exact ⟨_,_,CommonExec.built he execution⟩
end SourceRule5CommonV3
