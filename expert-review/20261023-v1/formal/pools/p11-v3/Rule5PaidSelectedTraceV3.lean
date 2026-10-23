import Rule5PaidRawProjectionV3

namespace SourceRule5PaidSelectionV3
open RMAF Universal233 WholeSourceWork SourceForestV3
open Universal233.Rule5FinalClassification Universal233.Rule5ExecutionSource
open Universal233.Rule5RemainingLocalWork
open SourceCouplingV2 (Mode)
open SourceDisjointV2 (ordinarySpec)
variable {OrdExec : Tree→Tree→Nat→Option F→Prop} {mode : Mode}
  {base : Tree→Tree→Nat→Option F} {T S : Tree}

theorem paid_selected_trace
    (sound : ∀ T S b a,OrdExec T S b a→a=base T S b)
    (h : SolvedExec OrdExec mode T S a b q k r slots) :
    (SourceRule5SelectedV3.paidReturn r).value=
      (Rule5ActualTrace.selectedTrace (ordinarySpec mode base) T S a b q (.remaining d (.second u v))).value ∧
    slots.map (fun s=>(s.index,s.query))=CallbackPairingAuthor.indexFrom k
      (Rule5ActualTrace.queries (ordinarySpec mode base)
        (Rule5ActualTrace.selectedTrace (ordinarySpec mode base) T S a b q (.remaining d (.second u v))).calls) := by
  cases h with
  | refused empty =>
    rw [prepare,paid_selected_value] at empty
    simp only [SourceRule5SelectedV3.paidReturn,Rule5ActualTrace.selectedTrace,empty,Rule5ActualTrace.queries]
    constructor <;> first | rfl | trivial
  | built found execution =>
    rw [prepare,paid_selected_value] at found
    have hv:=best_raw_projection sound execution
    have hi:=best_index sound execution
    simp only [SourceRule5SelectedV3.paidReturn,solvedReturn,Rule5ActualTrace.selectedTrace,found,Rule5ActualTrace.queries]
    constructor
    · exact congrArg Rule5OrdinaryDispatch.Result.answered hv.1
    · simpa only [hv.2] using hi
end SourceRule5PaidSelectionV3

namespace SourceRule5SelectedV3
open RMAF Universal233 WholeSourceWork SourceForestV3
open SourceCouplingV2 (Mode)
open SourceDisjointV2 (ordinarySpec)
variable {OrdExec : Tree→Tree→Nat→Option F→Prop} {mode : Mode}
  {base : Tree→Tree→Nat→Option F} {T S : Tree}

theorem selected_actual_trace
    (sound : ∀ T S b a,OrdExec T S b a→a=base T S b)
    (h : SelectedExec OrdExec mode T S a b q k z r slots) :
    r.value=(Rule5ActualTrace.selectedTrace (ordinarySpec mode base) T S a b q z).value ∧
    slots.map (fun s=>(s.index,s.query))=CallbackPairingAuthor.indexFrom k
      (Rule5ActualTrace.queries (ordinarySpec mode base)
        (Rule5ActualTrace.selectedTrace (ordinarySpec mode base) T S a b q z).calls) := by
  cases h with
  | prefixArm execution => exact SourceRule5SelectedArmV3.prefix_trace sound execution
  | firstArm execution => exact SourceRule5SelectedArmV3.first_trace sound execution
  | thirdArm execution => exact SourceRule5SelectedArmV3.third_trace sound execution
  | commonArm execution => exact SourceRule5CommonV3.common_selected_trace sound execution
  | paidArm execution => exact SourceRule5PaidSelectionV3.paid_selected_trace sound execution
end SourceRule5SelectedV3
