import Rule5CurrentRawProjectionV3

namespace SourceRule5SelectedArmV3
open RMAF Universal233 WholeSourceWork SourceForestV3
open Universal233.Rule5FinalClassification
open GenericForest.FrontierWork
open SourceCouplingV2 (Mode)
open SourceDisjointV2 (ordinarySpec)
variable {OrdExec : Tree→Tree→Nat→Option F→Prop} {mode : Mode}
  {base : Tree→Tree→Nat→Option F} {T S : Tree}

theorem prefix_trace
    (sound : ∀ T S b a,OrdExec T S b a→a=base T S b)
    (h : ArmExec OrdExec mode T S a b q k (.prefix s) r slots) :
    Rule5OrdinaryDispatch.Result.answered r.value=(Rule5ActualTrace.selectedTrace (ordinarySpec mode base) T S a b q (.prefix s)).value ∧
    slots.map (fun x=>(x.index,x.query))=CallbackPairingAuthor.indexFrom k
      (Rule5ActualTrace.queries (ordinarySpec mode base)
        (Rule5ActualTrace.selectedTrace (ordinarySpec mode base) T S a b q (.prefix s)).calls) := by
  have hv:=arm_raw_forest_jobs sound h
  simpa only [Rule5OrdinaryDispatch.selectedForestChildren,Rule5ActualTrace.selectedTrace,Rule5ActualTrace.queries] using
    And.intro (congrArg Rule5OrdinaryDispatch.Result.answered hv.1) hv.2

theorem first_trace
    (sound : ∀ T S b a,OrdExec T S b a→a=base T S b)
    (h : ArmExec OrdExec mode T S a b q k (.remaining d (.first u v)) r slots) :
    Rule5OrdinaryDispatch.Result.answered r.value=(Rule5ActualTrace.selectedTrace (ordinarySpec mode base) T S a b q (.remaining d (.first u v))).value ∧
    slots.map (fun x=>(x.index,x.query))=CallbackPairingAuthor.indexFrom k
      (Rule5ActualTrace.queries (ordinarySpec mode base)
        (Rule5ActualTrace.selectedTrace (ordinarySpec mode base) T S a b q (.remaining d (.first u v))).calls) := by
  have hv:=arm_raw_forest_jobs sound h
  simpa only [Rule5OrdinaryDispatch.selectedForestChildren,Rule5ActualTrace.selectedTrace,Rule5ActualTrace.queries] using
    And.intro (congrArg Rule5OrdinaryDispatch.Result.answered hv.1) hv.2

theorem third_trace
    (sound : ∀ T S b a,OrdExec T S b a→a=base T S b)
    (h : ArmExec OrdExec mode T S a b q k (.remaining d (.third u v)) r slots) :
    Rule5OrdinaryDispatch.Result.answered r.value=(Rule5ActualTrace.selectedTrace (ordinarySpec mode base) T S a b q (.remaining d (.third u v))).value ∧
    slots.map (fun x=>(x.index,x.query))=CallbackPairingAuthor.indexFrom k
      (Rule5ActualTrace.queries (ordinarySpec mode base)
        (Rule5ActualTrace.selectedTrace (ordinarySpec mode base) T S a b q (.remaining d (.third u v))).calls) := by
  have hv:=arm_raw_forest_jobs sound h
  simpa only [Rule5OrdinaryDispatch.selectedForestChildren,Rule5ActualTrace.selectedTrace,Rule5ActualTrace.queries] using
    And.intro (congrArg Rule5OrdinaryDispatch.Result.answered hv.1) hv.2
end SourceRule5SelectedArmV3
