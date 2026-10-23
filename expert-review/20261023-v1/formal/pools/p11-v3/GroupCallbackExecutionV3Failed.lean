import Rule5SelectedArmExecutionV3

namespace SourceGroupCallbackV3
open RMAF Universal233 WholeSourceWork CoreWork SourceForestV3
open OrdinaryDispatch.Hard2SourceWork OrdinaryDispatch.WorkIntegration
open GenericForest.FrontierWork Universal233.GroupedFullQuery
open SourceCouplingV2 (Mode enabled)
open SourceDisjointV2 (ordinarySpec)

def finish (p : Problem) (out : SourceForestV3.Result) : Charged (Option (Nat×F)) :=
  match out.value with
  | none=>⟨none,4⟩
  | some F=>let c:=additionalCostMeter p.sources F;⟨some (c.value,F),c.work+12⟩

inductive CallbackExec (OrdExec : Tree→Tree→Nat→Option F→Prop) (mode : Mode)
    (p : Problem) (b k : Nat) : Charged (Option (Nat×F))→Nat→List SourceForestV3.S→Prop
  | run (forest : ForestExec OrdExec mode k p.target p.sources b out) :
      CallbackExec OrdExec mode p b k (finish p out) out.debit out.slots

variable {OrdExec : Tree→Tree→Nat→Option F→Prop} {mode : Mode}
  {base : Tree→Tree→Nat→Option F}

theorem callback_fields
    (sound : ∀ T S b a,OrdExec T S b a→a=base T S b)
    (h : CallbackExec OrdExec mode p b k r debit slots) :
    r=groupCallbackMeter (ordinarySpec mode base) p b := by
  cases h with
  | run forest =>
    have hv:=(forest_correspondence sound _ _ _ _ _ forest).1
    simp only [finish,groupCallbackMeter,hv]

theorem callback_debit
    (sound : ∀ T S b a,OrdExec T S b a→a=base T S b)
    (h : CallbackExec OrdExec mode p b k r debit slots) :
    debit=OrdinaryDispatch.WorkRecursion.forestWork (ordinarySpec mode base) (fun _ _ _=>0) p.target p.sources b := by
  cases h with
  | run forest => exact (forest_correspondence sound _ _ _ _ _ forest).2.1

theorem callback_index
    (sound : ∀ T S b a,OrdExec T S b a→a=base T S b)
    (h : CallbackExec OrdExec mode p b k r debit slots) :
    slots.map (fun s=>(s.index,s.query))=CallbackPairingAuthor.indexFrom k
      (frontier (ordinarySpec mode base) p.target p.sources b) := by
  cases h with
  | run forest => exact (forest_correspondence sound _ _ _ _ _ forest).2.2

theorem callback_slots_realize (h : CallbackExec OrdExec mode p b k r debit slots) :
    ∀ s∈slots,SlotRealizes OrdExec mode s := by
  cases h with
  | run forest => exact forest_slots_realize _ _ _ _ _ forest

theorem callback_exists
    (total : ∀ T S b,enabled mode b=true→∃ a,OrdExec T S b a)
    (p : Problem) (b k : Nat) :
    ∃ r debit slots,CallbackExec OrdExec mode p b k r debit slots := by
  obtain ⟨out,execution⟩:=forest_exists total b k p.target p.sources
  exact ⟨_,_,_,CallbackExec.run execution⟩
end SourceGroupCallbackV3
