import GroupLedgersV3

namespace SourceBadPairV3
open RMAF Universal233 WholeSourceWork CoreWork SourceForestV3
open GenericForest.FrontierWork
open OrdinaryDispatch.Hard2SourceWork OrdinaryDispatch.WorkIntegration
open SourceCouplingV2 (Mode enabled)
open SourceDisjointV2 (ordinarySpec)

def agreesReturn (T S : Tree) (C : List Nat) (r : SourceExecution) : SourceExecution :=
  ⟨r.value,(meterRestrictionAgrees S T C).work+r.work+8⟩
def groupedReturn (T S : Tree) (C : List Nat) (r : GroupPairSourceExecution) : SourceExecution :=
  ⟨⟨r.value.answer,groupCalls r.value.queries⟩,
    (meterRestrictionAgrees S T C).work+r.work+12*r.value.queries.length+12⟩
def complete (r : SourceExecution) (debits : List Nat) : SourceExecution :=
  ⟨r.value,r.work+debits.sum⟩

inductive LocalExec (OrdExec : Tree→Tree→Nat→Option F→Prop) (mode : Mode)
    (T S : Tree) (A B C : List Nat) (edge : Vertex×Vertex) (q k : Nat) :
    SourceExecution→List Nat→List SourceForestV3.S→Prop
  | agrees (good : (meterRestrictionAgrees S T C).value=true)
      (execution : SourceBothBadPairV3.PairExec OrdExec mode T S A B C edge q k r debits slots) :
      LocalExec OrdExec mode T S A B C edge q k (agreesReturn T S C r) debits slots
  | grouped (bad : (meterRestrictionAgrees S T C).value≠true)
      (execution : SourceGroupPairV3.PairExec OrdExec mode T S A B C edge q k r debits slots) :
      LocalExec OrdExec mode T S A B C edge q k (groupedReturn T S C r) debits slots

variable {OrdExec : Tree→Tree→Nat→Option F→Prop} {mode : Mode}
  {base : Tree→Tree→Nat→Option F} {T S : Tree} {A B C : List Nat}

theorem bad_local_source_fields
    (sound : ∀ T S b a,OrdExec T S b a→a=base T S b)
    (h : LocalExec OrdExec mode T S A B C edge q k r debits slots) :
    r=badPairLocalSource (ordinarySpec mode base) T S A B C edge q := by
  cases h with
  | agrees good execution =>
    have hv:=SourceBothBadPairV3.pair_source_fields sound execution
    simp only [agreesReturn,badPairLocalSource,good,↓reduceIte,hv]
  | grouped bad execution =>
    have hv:=SourceGroupPairV3.pair_source_fields sound execution
    simp only [groupedReturn,badPairLocalSource,bad,↓reduceIte,hv]

theorem bad_debits
    (sound : ∀ T S b a,OrdExec T S b a→a=base T S b)
    (h : LocalExec OrdExec mode T S A B C edge q k r debits slots) :
    debits.sum=callsForestDebit (ordinarySpec mode base) (fun _ _ _=>0) r.value.calls := by
  cases h with
  | agrees good execution =>
    have hd:=SourceBothBadPairV3.pair_debits sound execution
    simpa only [agreesReturn] using hd
  | grouped bad execution =>
    have hd:=SourceGroupPairV3.pair_debits sound execution
    simpa only [groupedReturn] using hd

theorem bad_source_fields
    (sound : ∀ T S b a,OrdExec T S b a→a=base T S b)
    (h : LocalExec OrdExec mode T S A B C edge q k r debits slots) :
    complete r debits=badPairSource (ordinarySpec mode base) (fun _ _ _=>0) T S A B C edge q := by
  have hv:=bad_local_source_fields sound h
  have hd:=bad_debits sound h
  simp only [complete,badPairSource,←hv,hd]

theorem bad_index
    (sound : ∀ T S b a,OrdExec T S b a→a=base T S b)
    (h : LocalExec OrdExec mode T S A B C edge q k r debits slots) :
    slots.map (fun s=>(s.index,s.query))=CallbackPairingAuthor.indexFrom k
      (forestQueries (ordinarySpec mode base) r.value.calls) := by
  cases h with
  | agrees good execution =>
    have hi:=SourceBothBadPairV3.pair_index sound execution
    simpa only [agreesReturn] using hi
  | grouped bad execution =>
    have hi:=SourceGroupPairV3.pair_index sound execution
    simpa only [groupedReturn] using hi

theorem bad_slots_realize (h : LocalExec OrdExec mode T S A B C edge q k r debits slots) :
    ∀ s∈slots,SlotRealizes OrdExec mode s := by
  cases h with
  | agrees good execution => exact SourceBothBadPairV3.pair_slots_realize execution
  | grouped bad execution => exact SourceGroupPairV3.pair_slots_realize execution

theorem bad_exists
    (total : ∀ T S b,enabled mode b=true→∃ a,OrdExec T S b a)
    (T S : Tree) (A B C : List Nat) (edge : Vertex×Vertex) (q k : Nat) :
    ∃ r debits slots,LocalExec OrdExec mode T S A B C edge q k r debits slots := by
  by_cases good:(meterRestrictionAgrees S T C).value=true
  · obtain ⟨r,debits,slots,execution⟩:=SourceBothBadPairV3.pair_exists total T S A B C edge q k
    exact ⟨_,_,_,LocalExec.agrees good execution⟩
  · obtain ⟨r,debits,slots,execution⟩:=SourceGroupPairV3.pair_exists total T S A B C edge q k
    exact ⟨_,_,_,LocalExec.grouped good execution⟩
end SourceBadPairV3
