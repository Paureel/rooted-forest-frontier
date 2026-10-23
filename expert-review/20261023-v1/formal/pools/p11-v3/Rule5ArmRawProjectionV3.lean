import Hard2WholeSourceExecutionV3

namespace SourceRule5SelectedArmV3
open RMAF Universal233 WholeSourceWork SourceForestV3 SourceChildrenV2
open Universal233.Rule5SelectedLocalWork Universal233.Rule5FinalClassification
open GenericForest.FrontierWork OrdinaryDispatch.WorkIntegration OrdinaryDispatch.WorkRecursion
open SourceCouplingV2 (Mode)
open SourceDisjointV2 (ordinarySpec)
variable {OrdExec : Tree→Tree→Nat→Option F→Prop} {mode : Mode}
  {base : Tree→Tree→Nat→Option F} {T S : Tree}

-- Only selected_children_value is an imported audited pure-value interface here.
theorem arm_raw_forest_jobs
    (sound : ∀ T S b a,OrdExec T S b a→a=base T S b)
    (h : ArmExec OrdExec mode T S a b q k z r slots) :
    r.value=Rule5ActualTrace.runForestJobs (ordinarySpec mode base) T S q
        (Rule5OrdinaryDispatch.forestJobs T q (Rule5OrdinaryDispatch.selectedForestChildren S a b z)) ∧
    slots.map (fun s=>(s.index,s.query))=CallbackPairingAuthor.indexFrom k
      ((Rule5OrdinaryDispatch.forestJobs T q (Rule5OrdinaryDispatch.selectedForestChildren S a b z)).flatMap
        (fun j=>frontier (ordinarySpec mode base) j.target j.sources j.residual)) := by
  cases h with
  | run children =>
    have hv:=children_actual_trace sound children S
    have hi:=children_index sound children
    constructor
    · simpa only [finish,childrenTrace,Universal233.Rule5SelectedLocalWork.selected_children_value] using hv.1
    · simpa only [childrenQueries,Universal233.Rule5SelectedLocalWork.selected_children_value] using hi
end SourceRule5SelectedArmV3
