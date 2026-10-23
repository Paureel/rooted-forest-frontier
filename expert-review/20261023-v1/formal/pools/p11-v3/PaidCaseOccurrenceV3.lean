import PaidCaseExecutionV3

namespace SourcePaidCaseV3
open RMAF Universal233 SourceForestV3 GenericForest.FrontierWork
open SourceCouplingV2 (Mode)
open SourceDisjointV2 (ordinarySpec)
variable {OrdExec : Tree→Tree→Nat→Option F→Prop} {mode : Mode}
  {base : Tree→Tree→Nat→Option F} {T S : Tree}

theorem selected_distinct
    (sound : ∀ T S b a,OrdExec T S b a→a=base T S b)
    (h : SelectedExec OrdExec mode T S c q out route r recorded chronological) :
    recorded.Pairwise (fun a b=>a.1≠b.1) := by
  cases h with
  | empty => simp
  | good A B C execution =>
    have strict:=ledger_strict (SourceGoodPairV3.good_index sound execution)
    simp only [linear,List.pairwise_map]
    exact strict.imp (fun h he=>by have hz:=congrArg Prod.snd he;omega)
  | hard execution =>
    cases execution with
    | run outputs => exact SourceFullOutputsV3.recorded_distinct_ids sound outputs
  | bad A B C execution =>
    have strict:=ledger_strict (SourceBadPairV3.bad_index sound execution)
    simp only [linear,List.pairwise_map]
    exact strict.imp (fun h he=>by have hz:=congrArg Prod.snd he;omega)

theorem paid_query_projection
    (sound : ∀ T S b a,OrdExec T S b a→a=base T S b)
    (h : PaidExec OrdExec mode T S c q out r recorded chronological) :
    recorded.map (fun o=>o.2.query)=OrdinaryDispatch.WorkIntegration.forestQueries (ordinarySpec mode base) r.value.calls := by
  cases h with
  | run execution =>
    have hp:=selected_query_projection sound execution
    simpa only [finish] using hp

theorem paid_permutation
    (h : PaidExec OrdExec mode T S c q out r recorded chronological) :
    chronological.Perm recorded := by
  cases h with
  | run execution => exact selected_permutation execution

theorem paid_distinct
    (sound : ∀ T S b a,OrdExec T S b a→a=base T S b)
    (h : PaidExec OrdExec mode T S c q out r recorded chronological) :
    recorded.Pairwise (fun a b=>a.1≠b.1) := by
  cases h with
  | run execution => exact selected_distinct sound execution

theorem paid_slots_realize (h : PaidExec OrdExec mode T S c q out r recorded chronological) :
    ∀ o∈recorded,SlotRealizes OrdExec mode o.2 := by
  cases h with
  | run execution => exact selected_slots_realize execution
end SourcePaidCaseV3
