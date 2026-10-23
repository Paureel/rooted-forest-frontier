import BothBadEntryFoldV3

namespace SourceUnitCombineV3
open RMAF Universal233 WholeSourceWork Universal233.Rule5SelectedLocalWork
open GenericForest.FrontierWork OrdinaryDispatch.Hard2SourceWork OrdinaryDispatch.WorkIntegration
open OrdinaryDispatch.OuterSource
open SourceForestV3 SourceChildrenV2
open SourceCouplingV2 (Mode enabled)
open SourceDisjointV2 (ordinarySpec)

-- paid is the already executed result; the unit execution follows it in actual order.
def finish (T S : Tree) (a b q : Nat) (paid : BothBad.Execution)
    (r : ForestReceipt (List F)) (debits : List Nat) : SourceExecution :=
  let cs:=unitChildrenMeter S a b
  let units:=finishSource T S q r debits
  let calls:=unitCallsMeter S T a b q
  let best:=chooseMeter units.value paid.answer
  ⟨⟨best.value,calls.value++paid.calls⟩,
    cs.work+units.work+calls.work+best.work+calls.value.length+8⟩

inductive CombineExec (OrdExec : Tree→Tree→Nat→Option F→Prop) (mode : Mode)
    (T S : Tree) (a b q : Nat) (paid : BothBad.Execution) (k : Nat) :
    SourceExecution→List SourceForestV3.S→Prop
  | run (children : ChildrenExec OrdExec mode T q k (unitChildrenMeter S a b).value r debits slots) :
      CombineExec OrdExec mode T S a b q paid k (finish T S a b q paid r debits) slots

variable {OrdExec : Tree→Tree→Nat→Option F→Prop} {mode : Mode}
  {base : Tree→Tree→Nat→Option F} {T S : Tree}

theorem combine_source_fields
    (sound : ∀ T S b a,OrdExec T S b a→a=base T S b)
    (h : CombineExec OrdExec mode T S a b q paid k r slots) :
    r=combineSource (ordinarySpec mode base) (fun _ _ _=>0) T S a b q paid := by
  cases h with
  | run children =>
    have hc:=children_source_fields sound children S
    simp only [finish,combineSource,hc]

theorem unit_queries
    (h : ChildrenExec OrdExec mode T q k (unitChildrenMeter S a b).value r debits slots)
    (actual : GenericForest.FrontierWork.Ordinary) :
    forestQueries actual (unitCallsMeter S T a b q).value=
      childrenQueries actual T q (unitChildrenMeter S a b).value := by
  have general : ∀ cs : List CherryBranching.Child,
      forestQueries actual (cs.filterMap (fun c=>(CherryBranching.remaining q c).map
        (fun b=>⟨some T,c.sourceForest,b⟩)))=childrenQueries actual T q cs := by
    intro cs
    induction cs with
    | nil => rfl
    | cons c cs ih =>
      simp only [childrenQueries,Rule5OrdinaryDispatch.forestJobs] at ih ⊢
      simp only [List.filterMap_cons,Rule5OrdinaryDispatch.jobFor]
      cases he:CherryBranching.remaining q c with
      | none => simpa only [he,Option.map_none] using ih
      | some b =>
        simp only [he,Option.map_some,forestQueries,List.flatMap_cons] at ih ⊢
        rw [ih]
  exact general _

theorem combine_unit_index
    (sound : ∀ T S b a,OrdExec T S b a→a=base T S b)
    (h : CombineExec OrdExec mode T S a b q paid k r slots) :
    slots.map (fun s=>(s.index,s.query))=CallbackPairingAuthor.indexFrom k
      (forestQueries (ordinarySpec mode base) (unitCallsMeter S T a b q).value) := by
  cases h with
  | run children =>
    rw [unit_queries children]
    exact children_index sound children

theorem combine_slots_realize (h : CombineExec OrdExec mode T S a b q paid k r slots) :
    ∀ s∈slots,SlotRealizes OrdExec mode s := by
  cases h with
  | run children => exact children_slots_realize children

theorem combine_exists
    (total : ∀ T S b,enabled mode b=true→∃ a,OrdExec T S b a)
    (T S : Tree) (a b q k : Nat) (paid : BothBad.Execution) :
    ∃ r slots,CombineExec OrdExec mode T S a b q paid k r slots := by
  obtain ⟨r,debits,slots,execution⟩:=children_execution_exists total T q k (unitChildrenMeter S a b).value
  exact ⟨_,_,CombineExec.run execution⟩

end SourceUnitCombineV3
