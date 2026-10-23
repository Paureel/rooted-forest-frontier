import GroupedRawProjectionV3

namespace SourcePaidCaseV3
open RMAF Universal233 SourceForestV3 SourceCouplingV2
open OrdinaryDispatch.OuterSource
open SourceDisjointV2 (ordinarySpec)
variable {OrdExec : Tree→Tree→Nat→Option F→Prop} {mode : Mode}
  {base : Tree→Tree→Nat→Option F} {T S : Tree}

theorem selected_raw_execution
    (sound : ∀ T S b a,OrdExec T S b a→a=base T S b)
    (h : SelectedExec OrdExec mode T S c q out route r rec chrono) :
    r.value=paidRouteExecution (ordinarySpec mode base) T S c q out route := by
  cases h with
  | empty => rfl
  | good A B C execution => exact SourceGoodPairV3.good_raw_execution sound execution
  | hard execution => exact SourceFullOutputsV3.hard_paid_raw_execution sound execution
  | bad A B C execution =>
    have hv:=SourceBadPairV3.bad_raw_execution sound execution
    simpa only [SourceBadPairV3.complete,paidRouteExecution] using hv

theorem paid_raw_execution
    (sound : ∀ T S b a,OrdExec T S b a→a=base T S b)
    (h : PaidExec OrdExec mode T S c q out r rec chrono) :
    r.value=OrdinaryDispatch.Hard2Dispatcher.paidCase (ordinarySpec mode base) T S c q out := by
  cases h with
  | run execution =>
    have hv:=selected_raw_execution sound execution
    rw [paidOuterMeter_value] at hv
    exact hv
end SourcePaidCaseV3

namespace SourcePaidUnitsV3
open RMAF Universal233 SourceForestV3 SourceCouplingV2
open OrdinaryDispatch.WorkIntegration OrdinaryDispatch.OuterSource OrdinaryDispatch.CompleteSource
open SourceDisjointV2 (ordinarySpec)
variable {OrdExec : Tree→Tree→Nat→Option F→Prop} {mode : Mode}
  {base : Tree→Tree→Nat→Option F} {T S : Tree}

theorem paid_units_raw_value
    (sound : ∀ T S b a,OrdExec T S b a→a=base T S b)
    (h : PaidUnitsExec OrdExec mode T S c q out r rec chrono) :
    r.value=(OrdinaryDispatch.Hard2Combine.combine (ordinarySpec mode base) T S c.a c.b q
      (OrdinaryDispatch.Hard2Dispatcher.paidCase (ordinarySpec mode base) T S c q out)).answer := by
  cases h with
  | run paid units =>
    have hp:=SourcePaidCaseV3.paid_raw_execution sound paid
    have hu:=SourceUnitCombineV3.combine_raw_execution sound units
    simp only [finish,hu,hp]

theorem paid_units_raw_queries
    (sound : ∀ T S b a,OrdExec T S b a→a=base T S b)
    (h : PaidUnitsExec OrdExec mode T S c q out r rec chrono) :
    rec.map (fun o=>o.2.query)=forestQueries (ordinarySpec mode base)
      (OrdinaryDispatch.Hard2Combine.combine (ordinarySpec mode base) T S c.a c.b q
        (OrdinaryDispatch.Hard2Dispatcher.paidCase (ordinarySpec mode base) T S c q out)).calls := by
  obtain ⟨calls,hq,hcalls⟩:=paid_units_queries sound h
  cases h with
  | run paid units =>
    have hpf:=SourcePaidCaseV3.paid_source_fields sound paid
    have huf:=SourceUnitCombineV3.combine_source_fields sound units
    rw [←hpf,←huf] at hcalls
    have hp:=SourcePaidCaseV3.paid_raw_execution sound paid
    have hu:=SourceUnitCombineV3.combine_raw_execution sound units
    rw [hcalls,hu,hp] at hq
    exact hq
end SourcePaidUnitsV3
