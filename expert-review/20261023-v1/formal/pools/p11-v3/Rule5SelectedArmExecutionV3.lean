import PaidUnitOccurrenceV3

namespace SourceRule5SelectedArmV3
open RMAF Universal233 WholeSourceWork
open GenericForest.FrontierWork OrdinaryDispatch.FullSourceWork OrdinaryDispatch.WorkIntegration
open Universal233.Rule5SelectedLocalWork Universal233.Rule5FinalClassification
open SourceForestV3 SourceChildrenV2
open SourceCouplingV2 (Mode enabled)
open SourceDisjointV2 (ordinarySpec)

def finish (T S : Tree) (a b q : Nat) (z : FinalSelection)
    (r : ForestReceipt (List F)) (debits : List Nat) : Charged (Option F) :=
  let cs:=selectedChildrenMeter S a b z
  let ans:=finishSource T S q r debits
  ⟨ans.value,cs.work+ans.work+2⟩

inductive ArmExec (OrdExec : Tree→Tree→Nat→Option F→Prop) (mode : Mode)
    (T S : Tree) (a b q k : Nat) (z : FinalSelection) :
    Charged (Option F)→List SourceForestV3.S→Prop
  | run (children : ChildrenExec OrdExec mode T q k (selectedChildrenMeter S a b z).value r debits slots) :
      ArmExec OrdExec mode T S a b q k z (finish T S a b q z r debits) slots

variable {OrdExec : Tree→Tree→Nat→Option F→Prop} {mode : Mode}
  {base : Tree→Tree→Nat→Option F} {T S : Tree}

theorem arm_source_fields
    (sound : ∀ T S b a,OrdExec T S b a→a=base T S b)
    (h : ArmExec OrdExec mode T S a b q k z r slots) :
    r=selectedArmSource (ordinarySpec mode base) (fun _ _ _=>0) T S a b q z := by
  cases h with
  | run children =>
    have hv:=children_source_fields sound children S
    simp only [finish,selectedArmSource,hv]

theorem arm_index
    (sound : ∀ T S b a,OrdExec T S b a→a=base T S b)
    (h : ArmExec OrdExec mode T S a b q k z r slots) :
    slots.map (fun s=>(s.index,s.query))=CallbackPairingAuthor.indexFrom k
      (childrenQueries (ordinarySpec mode base) T q (selectedChildrenMeter S a b z).value) := by
  cases h with
  | run children => exact children_index sound children

theorem arm_slots_realize (h : ArmExec OrdExec mode T S a b q k z r slots) :
    ∀ s∈slots,SlotRealizes OrdExec mode s := by
  cases h with
  | run children => exact children_slots_realize children

theorem arm_exists
    (total : ∀ T S b,enabled mode b=true→∃ a,OrdExec T S b a)
    (T S : Tree) (a b q k : Nat) (z : FinalSelection) :
    ∃ r slots,ArmExec OrdExec mode T S a b q k z r slots := by
  obtain ⟨r,debits,slots,execution⟩:=children_execution_exists total T q k (selectedChildrenMeter S a b z).value
  exact ⟨_,_,ArmExec.run execution⟩

end SourceRule5SelectedArmV3
