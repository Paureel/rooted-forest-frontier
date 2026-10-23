import BothBadDispatchExecutionV3

namespace SourceBothBadFoldV3
open RMAF Universal233 WholeSourceWork CoreWork
open GenericForest GenericForest.FrontierWork GenericForest.CheckCorrespondence
open OrdinaryDispatch.Hard2SourceWork OrdinaryDispatch.WorkIntegration
open Universal233.BothBad SourceForestV3
open SourceDisjointV2 (ordinarySpec)

def prepend (T S : Tree) (q : Nat) (r tail : SourceExecution) : SourceExecution :=
  let checked:=checkedMeter T S q r.value.answer
  let best:=chooseMeter checked.value tail.value.answer
  ⟨⟨best.value,r.value.calls++tail.value.calls⟩,
    r.work+tail.work+checked.work+best.work+2*r.value.calls.length+20⟩

inductive EntriesExec (OrdExec : Tree→Tree→Nat→Option F→Prop) (mode : SourceCouplingV2.Mode)
    (T S : Tree) (q : Nat) : Nat→List Entry→SourceExecution→List Nat→List SourceForestV3.S→Prop
  | nil : EntriesExec OrdExec mode T S q k [] ⟨⟨none,[]⟩,2⟩ [] []
  | cons (head : SourceBothBadDispatchV3.DispatchExec OrdExec mode T S e k r debits slots)
      (tail : EntriesExec OrdExec mode T S q (k+slots.length) es rr dd ss) :
      EntriesExec OrdExec mode T S q k (e::es) (prepend T S q r rr) (debits++dd) (slots++ss)

variable {OrdExec : Tree→Tree→Nat→Option F→Prop} {mode : SourceCouplingV2.Mode}
  {base : Tree→Tree→Nat→Option F} {T S : Tree}

theorem entries_source_fields
    (sound : ∀ T S b a,OrdExec T S b a→a=base T S b)
    (h : EntriesExec OrdExec mode T S q k es r debits slots) :
    r=bothBadExecuteLocalSource (ordinarySpec mode base) T S q es := by
  induction h with
  | nil => rfl
  | cons head tail ih =>
    have hv:=SourceBothBadDispatchV3.dispatch_source_fields sound head
    simp only [bothBadExecuteLocalSource,prepend,hv,ih]

theorem entries_debits
    (sound : ∀ T S b a,OrdExec T S b a→a=base T S b)
    (h : EntriesExec OrdExec mode T S q k es r debits slots) :
    debits.sum=callsForestDebit (ordinarySpec mode base) (fun _ _ _=>0) r.value.calls := by
  induction h with
  | nil => rfl
  | cons head tail ih =>
    have hd:=SourceBothBadDispatchV3.dispatch_debits sound head
    simp only [prepend,callsForestDebit,List.map_append,List.sum_append] at hd ih ⊢
    rw [hd,ih]

theorem entries_index
    (sound : ∀ T S b a,OrdExec T S b a→a=base T S b)
    (h : EntriesExec OrdExec mode T S q k es r debits slots) :
    slots.map (fun s=>(s.index,s.query))=CallbackPairingAuthor.indexFrom k
      (forestQueries (ordinarySpec mode base) r.value.calls) := by
  induction h with
  | nil => rfl
  | @cons k e r debits slots es rr dd ss head tail ih =>
    have hi:=SourceBothBadDispatchV3.dispatch_index sound head
    have hl:=SourceForestV3.index_length hi
    simp only [List.map_append,hi,ih,hl,prepend,forestQueries,List.flatMap_append]
    exact (SourceForestV3.indexFrom_append _ _ _).symm

theorem entries_slots_realize (h : EntriesExec OrdExec mode T S q k es r debits slots) :
    ∀ s∈slots,SlotRealizes OrdExec mode s := by
  induction h with
  | nil => simp
  | cons head tail ih =>
    intro s hs
    rcases List.mem_append.mp hs with hs|hs
    · exact SourceBothBadDispatchV3.dispatch_slots_realize head s hs
    · exact ih s hs

end SourceBothBadFoldV3
