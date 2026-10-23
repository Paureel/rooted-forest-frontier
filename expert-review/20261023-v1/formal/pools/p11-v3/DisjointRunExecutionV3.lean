import DisjointQueryExecutionV3

namespace SourceDisjointRunV3
open RMAF Universal233 WholeSourceWork Universal233.Rule5SelectedLocalWork
open GenericForest.FrontierWork OrdinaryDispatch.Hard2SourceWork OrdinaryDispatch.WorkIntegration
open SourceForestV3 SourceChildrenV2 SourceDisjointQueryV3
open SourceCouplingV2 (Mode enabled)
open SourceDisjointV2 (ordinarySpec)

def childrenCalls (T : Tree) (r : ForestReceipt (List F)) : List BothBad.Call :=
  r.calls.map (fun c=>⟨some T,c.child.sourceForest,c.budget⟩)

def finish (T S : Tree) (a b q : Nat) (r : ForestReceipt (List F)) (debits : List Nat)
    (qr : SourceExecution) : Charged (Option F) :=
  let x:=singletonChildMeter S a
  let y:=singletonChildMeter S b
  let cs:=finishSource T S q r debits
  let p:=Rule5PendantLocalWork.partitionMeter S a b
  let best:=chooseMeter cs.value qr.value.answer
  ⟨best.value,x.work+y.work+cs.work+p.work+qr.work+best.work+12⟩

inductive DisjointExec (OrdExec : Tree→Tree→Nat→Option F→Prop) (mode : Mode)
    (T S : Tree) (a b q : Nat) : Charged (Option F)→List BothBad.Call→List SourceForestV3.S→Prop
  | run (children : ChildrenExec OrdExec mode T q 0
        [(singletonChildMeter S a).value,(singletonChildMeter S b).value] r debits slots)
      (query : QueryExec OrdExec mode T S (Rule5PendantLocalWork.partitionMeter S a b).value
        q slots.length qr qslots) :
      DisjointExec OrdExec mode T S a b q (finish T S a b q r debits qr)
        (childrenCalls T r++qr.value.calls) (slots++qslots)

variable {OrdExec : Tree→Tree→Nat→Option F→Prop} {mode : Mode}
  {base : Tree→Tree→Nat→Option F} {T S : Tree}

theorem children_calls_queries
    (h : ChildrenExec OrdExec mode T q k cs r debits slots)
    (actual : GenericForest.FrontierWork.Ordinary) :
    forestQueries actual (childrenCalls T r)=childrenQueries actual T q cs := by
  obtain ⟨ticks,ht⟩:=children_forget h
  have hc:=children_jobs ht
  simp only [childrenQueries]
  rw [←hc]
  simp only [forestQueries,childrenCalls,List.flatMap_map,queryJob,Function.comp_def]

theorem disjoint_source_fields
    (sound : ∀ T S b a,OrdExec T S b a→a=base T S b)
    (h : DisjointExec OrdExec mode T S a b q out calls slots) :
    out=disjointRunSource (ordinarySpec mode base) (fun _ _ _=>0) T S a b q := by
  cases h with
  | run children query =>
    have hc:=children_source_fields sound children S
    have hq:=query_source_fields sound query
    simp only [finish,disjointRunSource,hc,hq]

theorem disjoint_index
    (sound : ∀ T S b a,OrdExec T S b a→a=base T S b)
    (h : DisjointExec OrdExec mode T S a b q out calls slots) :
    slots.map (fun s=>(s.index,s.query))=CallbackPairingAuthor.indexFrom 0
      (forestQueries (ordinarySpec mode base) calls) := by
  cases h with
  | run children query =>
    have hc:=children_index sound children
    rw [←children_calls_queries children] at hc
    have hq:=query_index sound query
    have hl:=index_length hc
    rw [List.map_append,hc,hq,hl]
    simp only [forestQueries,List.flatMap_append,indexFrom_append,Nat.zero_add]

theorem disjoint_exists
    (total : ∀ T S b,enabled mode b=true→∃ a,OrdExec T S b a)
    (T S : Tree) (a b q : Nat) : ∃ out calls slots,DisjointExec OrdExec mode T S a b q out calls slots := by
  obtain ⟨r,debits,slots,children⟩:=children_execution_exists total T q 0
    [(singletonChildMeter S a).value,(singletonChildMeter S b).value]
  obtain ⟨qr,qslots,query⟩:=query_exists total T S (Rule5PendantLocalWork.partitionMeter S a b).value q slots.length
  exact ⟨_,_,_,DisjointExec.run children query⟩

end SourceDisjointRunV3
