import OrdinaryLocalRawProjectionV3

namespace SourceDisjointRunV3
open RMAF Universal233 SourceForestV3 SourceCouplingV2 SourceChildrenV2
open Universal233.CherryBranching OrdinaryDispatch.WorkIntegration
open SourceChildMetadataV3 SourcePendantValuesV3 SourceHard2ValuesV3
open SourceDisjointV2 (ordinarySpec)
variable {OrdExec : Tree→Tree→Nat→Option F→Prop} {mode : Mode}
  {base : Tree→Tree→Nat→Option F} {T S : Tree}

theorem children_calls_raw
    (h : ChildrenExec OrdExec mode T q k cs r debits slots) :
    childrenCalls T r=cs.filterMap (fun c=>(remaining q c).map
      (fun b=>BothBad.Call.mk (some T) c.sourceForest b)) := by
  induction h with
  | nil => rfl
  | refused over tail ih =>
    simpa only [childrenCalls,prependChild,List.map_append,List.map_nil,List.nil_append,
      List.filterMap_cons,remaining,over,↓reduceIte,Option.map_none] using ih
  | returned paid execution tail ih =>
    simp only [childrenCalls,prependChild,List.map_append,List.map_cons,List.map_nil,
      List.nil_append,List.cons_append,List.filterMap_cons,remaining,paid,↓reduceIte,Option.map_some] at ih ⊢
    exact congrArg (List.cons _) ih

-- The raw helper is only a returned value/stored-list view. Actual source order is units then query.
theorem disjoint_raw_trace
    (sound : ∀ T S b a,OrdExec T S b a→a=base T S b)
    (h : DisjointExec OrdExec mode T S a b q r calls slots) :
    r.value=(OrdinaryDispatch.Hard2Trace.disjointExecution (ordinarySpec mode base) T S a b q).answer ∧
    calls=(OrdinaryDispatch.Hard2Trace.disjointExecution (ordinarySpec mode base) T S a b q).calls := by
  cases h with
  | run children query =>
    have hc:=children_parent_raw sound children S
    have hq:=SourceDisjointQueryV3.query_raw_execution sound query
    have hcalls:=children_calls_raw children
    rw [singletonChild_value,singletonChild_value] at hc hcalls
    rw [partition_value] at hq
    simp only [finish,choose_value,hc,hq,OrdinaryDispatch.Hard2Trace.disjointExecution,
      OrdinaryDispatch.Hard2Combine.combine,OrdinaryDispatch.Hard2Combine.unitCalls,hcalls]
    constructor <;> first | rfl | trivial

theorem disjoint_trace_index
    (sound : ∀ T S b a,OrdExec T S b a→a=base T S b)
    (h : DisjointExec OrdExec mode T S a b q r calls slots) :
    slots.map (fun s=>(s.index,s.query))=CallbackPairingAuthor.indexFrom 0
      (forestQueries (ordinarySpec mode base)
        (OrdinaryDispatch.Hard2Trace.disjointExecution (ordinarySpec mode base) T S a b q).calls) := by
  have hi:=disjoint_index sound h
  rw [(disjoint_raw_trace sound h).2] at hi
  exact hi
end SourceDisjointRunV3
