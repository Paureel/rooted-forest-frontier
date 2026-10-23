import Rule5CommonRawProjectionV3
import Rule5ArmSelectedTraceV3

namespace SourceRule5CommonV3
open RMAF Universal233 WholeSourceWork SourceForestV3
open Universal233.Rule5FinalClassification
open SourceCouplingV2 (Mode)
open SourceDisjointV2 (ordinarySpec)
variable {OrdExec : Tree→Tree→Nat→Option F→Prop} {mode : Mode}
  {base : Tree→Tree→Nat→Option F} {T S : Tree}

theorem common_selected_trace
    (sound : ∀ T S b a,OrdExec T S b a→a=base T S b)
    (h : CommonExec OrdExec mode T S a b q k d r slots) :
    Rule5OrdinaryDispatch.Result.answered r.value=
      (Rule5ActualTrace.selectedTrace (ordinarySpec mode base) T S a b q (.remaining d (.one x))).value ∧
    slots.map (fun s=>(s.index,s.query))=CallbackPairingAuthor.indexFrom k
      (Rule5ActualTrace.queries (ordinarySpec mode base)
        (Rule5ActualTrace.selectedTrace (ordinarySpec mode base) T S a b q (.remaining d (.one x))).calls) := by
  have hv:=common_actual_trace sound h
  simpa only [Rule5ActualTrace.selectedTrace,Rule5ActualTrace.queries] using
    And.intro (congrArg Rule5OrdinaryDispatch.Result.answered hv.1) hv.2
end SourceRule5CommonV3
