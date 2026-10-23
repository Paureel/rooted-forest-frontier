import MafScheduleRawProjectionV3

namespace SourceOrdinaryMafRawV3
open RMAF Universal233 WholeSourceWork CoreWork
open OrdinaryDispatch.Hard2SourceWork

theorem local_raw_value (actual : GenericForest.FrontierWork.Ordinary)
    (T S : Tree) (Q : List (List Nat)) (b : Nat) :
    (ordinaryLocalSource actual T S Q b).value=
      BothBad.ordinaryExecution (GenericForest.solve actual) T S Q b := by
  simp only [ordinaryLocalSource,ordinaryPrepareMeter_value,BothBad.ordinaryExecution]
  cases hp:MafScheduler.prepare T S Q with
  | none => rfl
  | some js =>
    have hv:=maf_schedule_retained actual T S b js
    simp only [flatten_value,query_list_value,hv.1,hv.2]
    rfl

end SourceOrdinaryMafRawV3

namespace SourceOrdinaryLocalV3
open RMAF Universal233 SourceForestV3 SourceCouplingV2
open SourceDisjointV2 (ordinarySpec)
variable {OrdExec : Tree→Tree→Nat→Option F→Prop} {mode : Mode}
  {base : Tree→Tree→Nat→Option F} {T S : Tree} {Q : List (List Nat)}

theorem local_raw_execution
    (sound : ∀ T S b a,OrdExec T S b a→a=base T S b)
    (h : LocalExec OrdExec mode T S Q b k r debits slots) :
    r.value=BothBad.ordinaryExecution (GenericForest.solve (ordinarySpec mode base)) T S Q b := by
  rw [local_source_fields sound h,SourceOrdinaryMafRawV3.local_raw_value]
end SourceOrdinaryLocalV3

namespace SourceDisjointQueryV3
open RMAF Universal233 SourceForestV3 SourceCouplingV2
open OrdinaryDispatch.Hard2SourceWork
open SourceDisjointV2 (ordinarySpec)
variable {OrdExec : Tree→Tree→Nat→Option F→Prop} {mode : Mode}
  {base : Tree→Tree→Nat→Option F} {T S : Tree}

theorem query_raw_execution
    (sound : ∀ T S b a,OrdExec T S b a→a=base T S b)
    (h : QueryExec OrdExec mode T S parts q k r slots) :
    r.value=OrdinaryDispatch.DisjointParents.query (ordinarySpec mode base) T S parts q := by
  cases h with
  | refused over => simp only [OrdinaryDispatch.DisjointParents.query,over,↓reduceIte]
  | returned paid execution =>
    have hv:=SourceOrdinaryLocalV3.local_raw_execution sound execution
    simp only [finish,checkedMeter_value,OrdinaryDispatch.DisjointParents.query,paid,↓reduceIte,hv]
end SourceDisjointQueryV3

namespace SourceDisjointRunV3
open RMAF Universal233 SourceForestV3 SourceCouplingV2
open SourceChildMetadataV3 SourcePendantValuesV3 SourceHard2ValuesV3
open SourceDisjointV2 (ordinarySpec)
variable {OrdExec : Tree→Tree→Nat→Option F→Prop} {mode : Mode}
  {base : Tree→Tree→Nat→Option F} {T S : Tree}

theorem disjoint_raw_value
    (sound : ∀ T S b a,OrdExec T S b a→a=base T S b)
    (h : DisjointExec OrdExec mode T S a b q r calls slots) :
    r.value=OrdinaryDispatch.DisjointParents.run (ordinarySpec mode base) T S a b q := by
  cases h with
  | run children query =>
    have hc:=children_parent_raw sound children S
    have hq:=SourceDisjointQueryV3.query_raw_execution sound query
    rw [singletonChild_value,singletonChild_value] at hc
    rw [partition_value] at hq
    simp only [finish,choose_value,hc,hq,OrdinaryDispatch.DisjointParents.run]
end SourceDisjointRunV3
