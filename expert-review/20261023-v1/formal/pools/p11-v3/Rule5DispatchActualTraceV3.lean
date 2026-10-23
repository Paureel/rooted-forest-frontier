import Rule5PaidSelectedTraceV3

namespace SourceRule5DispatchV3
open RMAF Universal233 WholeSourceWork SourceForestV3
open Universal233.Rule5PendantLocalWork
open SourceCouplingV2 (Mode)
open SourceDisjointV2 (ordinarySpec)
variable {OrdExec : Tree→Tree→Nat→Option F→Prop} {mode : Mode}
  {base : Tree→Tree→Nat→Option F} {T S : Tree}

theorem dispatch_actual_trace
    (sound : ∀ T S b a,OrdExec T S b a→a=base T S b)
    (h : DispatchExec OrdExec mode T S a b q k r slots) :
    r.value=(Rule5ActualTrace.dispatchTrace (ordinarySpec mode base) T S a b q).value ∧
    slots.map (fun s=>(s.index,s.query))=CallbackPairingAuthor.indexFrom k
      (Rule5ActualTrace.queries (ordinarySpec mode base)
        (Rule5ActualTrace.dispatchTrace (ordinarySpec mode base) T S a b q).calls) := by
  cases h with
  | refused empty =>
    rw [final_value] at empty
    simp only [Rule5ActualTrace.dispatchTrace,empty,Rule5ActualTrace.queries]
    constructor <;> first | rfl | trivial
  | selected found execution =>
    rw [final_value] at found
    have hv:=SourceRule5SelectedV3.selected_actual_trace sound execution
    simpa only [finish,Rule5ActualTrace.dispatchTrace,found] using hv

theorem dispatch_answer_actual_trace
    (sound : ∀ T S b a,OrdExec T S b a→a=base T S b)
    (h : DispatchExec OrdExec mode T S a b q k r slots) :
    (answerView r).value=Rule5ActualTrace.answer
      (Rule5ActualTrace.dispatchTrace (ordinarySpec mode base) T S a b q) ∧
    slots.map (fun s=>(s.index,s.query))=CallbackPairingAuthor.indexFrom k
      (Rule5ActualTrace.queries (ordinarySpec mode base)
        (Rule5ActualTrace.dispatchTrace (ordinarySpec mode base) T S a b q).calls) := by
  have hv:=dispatch_actual_trace sound h
  constructor
  · simp only [answerView,Rule5ActualTrace.answer,hv.1]
    rfl
  · exact hv.2
end SourceRule5DispatchV3
