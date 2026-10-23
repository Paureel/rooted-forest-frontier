import DisjointSlotRealizationV3

namespace SourceBothBadDispatchV3
open RMAF Universal233 WholeSourceWork CoreWork
open GenericForest GenericForest.FrontierWork GenericForest.CheckCorrespondence
open OrdinaryDispatch.Hard2SourceWork OrdinaryDispatch.WorkIntegration
open Universal233.BothBad Universal233.Rule5SelectedLocalWork
open SourceForestV3 SourceCouplingV2
open SourceDisjointV2 (ordinarySpec)

-- These are the literal local views; forest debits remain a separate collected field.
def fullReturn (T S : Tree) (e : Entry) (out : SourceForestV3.Result) : SourceExecution :=
  let ss:=sourceForestMeter S e.output.partition
  ⟨⟨out.value,[⟨some T,ss.value,e.budget⟩]⟩,ss.work+16⟩

def retainedReturn (T S : Tree) (e : Entry) (residual completed : List Nat)
    (known : F) (out : SourceForestV3.Result) : SourceExecution :=
  let t:=localTargetMeter (some T) residual
  let sf:=sourceForestMeter S e.output.partition
  let bs:=ownedMeter sf.value residual
  let f:=retainedReconstructionMeter known completed out.value
  ⟨⟨f.value,[⟨t.value,bs.value,e.budget⟩]⟩,t.work+sf.work+bs.work+f.work+20⟩

inductive DispatchExec (OrdExec : Tree→Tree→Nat→Option F→Prop) (mode : SourceCouplingV2.Mode)
    (T S : Tree) (e : Entry) (k : Nat) : SourceExecution→List Nat→List SourceForestV3.S→Prop
  | ordinary (selected : e.mode=.ordinary)
      (execution : SourceOrdinaryLocalV3.LocalExec OrdExec mode T S e.output.partition e.budget k r debits slots) :
      DispatchExec OrdExec mode T S e k r debits slots
  | full (selected : e.mode=.full)
      (execution : ForestExec OrdExec mode k (some T) (sourceForestMeter S e.output.partition).value e.budget out) :
      DispatchExec OrdExec mode T S e k (fullReturn T S e out) [out.debit] out.slots
  | retained (selected : e.mode=.retained parent residual completed known)
      (execution : ForestExec OrdExec mode k (localTargetMeter (some T) residual).value
        (ownedMeter (sourceForestMeter S e.output.partition).value residual).value e.budget out) :
      DispatchExec OrdExec mode T S e k (retainedReturn T S e residual completed known out) [out.debit] out.slots

variable {OrdExec : Tree→Tree→Nat→Option F→Prop} {mode : SourceCouplingV2.Mode}
  {base : Tree→Tree→Nat→Option F} {T S : Tree} {e : Entry}

theorem dispatch_source_fields
    (sound : ∀ T S b a,OrdExec T S b a→a=base T S b)
    (h : DispatchExec OrdExec mode T S e k r debits slots) :
    r=bothBadDispatchLocalSource (ordinarySpec mode base) T S e := by
  cases h with
  | ordinary selected execution =>
    simpa only [bothBadDispatchLocalSource,selected] using SourceOrdinaryLocalV3.local_source_fields sound execution
  | full selected execution =>
    have hv:=(forest_correspondence sound _ _ _ _ _ execution).1
    simp only [bothBadDispatchLocalSource,selected,fullReturn,hv]
  | retained selected execution =>
    have hv:=(forest_correspondence sound _ _ _ _ _ execution).1
    simp only [bothBadDispatchLocalSource,selected,retainedReturn,hv]

theorem dispatch_debits
    (sound : ∀ T S b a,OrdExec T S b a→a=base T S b)
    (h : DispatchExec OrdExec mode T S e k r debits slots) :
    debits.sum=callsForestDebit (ordinarySpec mode base) (fun _ _ _=>0) r.value.calls := by
  cases h with
  | ordinary selected execution => exact SourceOrdinaryLocalV3.local_debits sound execution
  | full selected execution =>
    have hd:=(forest_correspondence sound _ _ _ _ _ execution).2.1
    simpa only [fullReturn,callsForestDebit,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,Nat.add_zero] using hd
  | retained selected execution =>
    have hd:=(forest_correspondence sound _ _ _ _ _ execution).2.1
    simpa only [retainedReturn,callsForestDebit,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,Nat.add_zero] using hd

theorem dispatch_index
    (sound : ∀ T S b a,OrdExec T S b a→a=base T S b)
    (h : DispatchExec OrdExec mode T S e k r debits slots) :
    slots.map (fun s=>(s.index,s.query))=CallbackPairingAuthor.indexFrom k
      (forestQueries (ordinarySpec mode base) r.value.calls) := by
  cases h with
  | ordinary selected execution => exact SourceOrdinaryLocalV3.local_index sound execution
  | full selected execution =>
    simpa only [fullReturn,forestQueries,List.flatMap_cons,List.flatMap_nil,List.append_nil] using
      (forest_correspondence sound _ _ _ _ _ execution).2.2
  | retained selected execution =>
    simpa only [retainedReturn,forestQueries,List.flatMap_cons,List.flatMap_nil,List.append_nil] using
      (forest_correspondence sound _ _ _ _ _ execution).2.2

theorem dispatch_slots_realize (h : DispatchExec OrdExec mode T S e k r debits slots) :
    ∀ s∈slots,SlotRealizes OrdExec mode s := by
  cases h with
  | ordinary selected execution => exact SourceOrdinaryLocalV3.local_slots_realize execution
  | full selected execution => exact forest_slots_realize _ _ _ _ _ execution
  | retained selected execution => exact forest_slots_realize _ _ _ _ _ execution

end SourceBothBadDispatchV3
