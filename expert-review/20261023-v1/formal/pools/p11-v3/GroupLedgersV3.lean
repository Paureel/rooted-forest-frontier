import GroupPairExecutionV3

namespace SourceGroupOutputV3
open RMAF Universal233 WholeSourceWork SourceForestV3
open OrdinaryDispatch.Hard2SourceWork OrdinaryDispatch.WorkIntegration
open SourceCouplingV2 (Mode)
open SourceDisjointV2 (ordinarySpec)
variable {OrdExec : Tree→Tree→Nat→Option F→Prop} {mode : Mode}
  {base : Tree→Tree→Nat→Option F} {T S : Tree} {A B C : List Nat}

theorem output_debits
    (sound : ∀ T S b a,OrdExec T S b a→a=base T S b)
    (h : OutputExec OrdExec mode T S A B C q k o r debits slots) :
    debits.sum=callsForestDebit (ordinarySpec mode base) (fun _ _ _=>0) (groupCalls r.value.trace) := by
  cases h with
  | unaffordable over => rfl
  | refused paid empty => rfl
  | scheduled paid found execution =>
    have hd:=SourceGroupLiteralV3.schedule_debits sound execution
    simpa only [finish,BothBadGrouped.OutputResult.trace] using hd

theorem output_index
    (sound : ∀ T S b a,OrdExec T S b a→a=base T S b)
    (h : OutputExec OrdExec mode T S A B C q k o r debits slots) :
    slots.map (fun s=>(s.index,s.query))=CallbackPairingAuthor.indexFrom k
      (forestQueries (ordinarySpec mode base) (groupCalls r.value.trace)) := by
  cases h with
  | unaffordable over => rfl
  | refused paid empty => rfl
  | scheduled paid found execution =>
    have hi:=SourceGroupLiteralV3.schedule_index sound execution
    simpa only [finish,BothBadGrouped.OutputResult.trace] using hi
end SourceGroupOutputV3

namespace SourceGroupEvaluationV3
open RMAF Universal233 WholeSourceWork SourceForestV3
open OrdinaryDispatch.Hard2SourceWork OrdinaryDispatch.WorkIntegration
open SourceCouplingV2 (Mode)
open SourceDisjointV2 (ordinarySpec)
variable {OrdExec : Tree→Tree→Nat→Option F→Prop} {mode : Mode}
  {base : Tree→Tree→Nat→Option F} {T S : Tree} {A B C : List Nat}

theorem evaluation_debits
    (sound : ∀ T S b a,OrdExec T S b a→a=base T S b)
    (h : EvaluationExec OrdExec mode T S A B C q k os r debits slots) :
    debits.sum=callsForestDebit (ordinarySpec mode base) (fun _ _ _=>0) (groupCalls r.value.queries) := by
  induction h with
  | nil => rfl
  | cons head tail ih =>
    have hd:=SourceGroupOutputV3.output_debits sound head
    simp only [prepend,List.sum_append,groupCalls,List.map_append,callsForestDebit,List.sum_append] at hd ih ⊢
    rw [hd,ih]

theorem evaluation_index
    (sound : ∀ T S b a,OrdExec T S b a→a=base T S b)
    (h : EvaluationExec OrdExec mode T S A B C q k os r debits slots) :
    slots.map (fun s=>(s.index,s.query))=CallbackPairingAuthor.indexFrom k
      (forestQueries (ordinarySpec mode base) (groupCalls r.value.queries)) := by
  induction h with
  | nil => rfl
  | @cons k o r debits slots os rr dd ss head tail ih =>
    have hi:=SourceGroupOutputV3.output_index sound head
    have hl:=index_length hi
    simp only [List.map_append,hi,ih,hl,prepend,groupCalls,List.map_append,forestQueries,List.flatMap_append]
    exact (indexFrom_append _ _ _).symm
end SourceGroupEvaluationV3

namespace SourceGroupPairV3
open RMAF Universal233 WholeSourceWork SourceForestV3
open OrdinaryDispatch.Hard2SourceWork OrdinaryDispatch.WorkIntegration
open SourceCouplingV2 (Mode)
open SourceDisjointV2 (ordinarySpec)
variable {OrdExec : Tree→Tree→Nat→Option F→Prop} {mode : Mode}
  {base : Tree→Tree→Nat→Option F} {T S : Tree} {A B C : List Nat}

theorem pair_debits
    (sound : ∀ T S b a,OrdExec T S b a→a=base T S b)
    (h : PairExec OrdExec mode T S A B C edge q k r debits slots) :
    debits.sum=callsForestDebit (ordinarySpec mode base) (fun _ _ _=>0) (groupCalls r.value.queries) := by
  cases h with
  | run execution =>
    have hd:=SourceGroupEvaluationV3.evaluation_debits sound execution
    simpa only [finish] using hd

theorem pair_index
    (sound : ∀ T S b a,OrdExec T S b a→a=base T S b)
    (h : PairExec OrdExec mode T S A B C edge q k r debits slots) :
    slots.map (fun s=>(s.index,s.query))=CallbackPairingAuthor.indexFrom k
      (forestQueries (ordinarySpec mode base) (groupCalls r.value.queries)) := by
  cases h with
  | run execution =>
    have hi:=SourceGroupEvaluationV3.evaluation_index sound execution
    simpa only [finish] using hi
end SourceGroupPairV3
