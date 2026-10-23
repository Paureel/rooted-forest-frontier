import Rule5SelectedExecutionV3

namespace SourceRule5DispatchV3
open RMAF Universal233 WholeSourceWork SourceForestV3
open Universal233.Rule5ExecutionSource Universal233.Rule5PendantLocalWork
open Universal233.ClassifierCheckFee Universal233.PaidLiteralDecisionWork
open SourceCouplingV2 (Mode enabled)
open SourceDisjointV2 (ordinarySpec)

def finish (T S : Tree) (a b : Nat) (r : Charged Rule5OrdinaryDispatch.Result) : Charged Rule5OrdinaryDispatch.Result :=
  ⟨r.value,(finalMeter checkFee T S a b).work+r.work+2⟩
inductive DispatchExec (OrdExec : Tree→Tree→Nat→Option F→Prop) (mode : Mode)
    (T S : Tree) (a b q k : Nat) : Charged Rule5OrdinaryDispatch.Result→List SourceForestV3.S→Prop
  | refused (empty : (finalMeter checkFee T S a b).value=none) :
      DispatchExec OrdExec mode T S a b q k ⟨.selectorRefused,(finalMeter checkFee T S a b).work+2⟩ []
  | selected (found : (finalMeter checkFee T S a b).value=some z)
      (execution : SourceRule5SelectedV3.SelectedExec OrdExec mode T S a b q k z r slots) :
      DispatchExec OrdExec mode T S a b q k (finish T S a b r) slots

variable {OrdExec : Tree→Tree→Nat→Option F→Prop} {mode : Mode}
  {base : Tree→Tree→Nat→Option F} {T S : Tree}

theorem dispatch_source_fields
    (sound : ∀ T S b a,OrdExec T S b a→a=base T S b)
    (h : DispatchExec OrdExec mode T S a b q k r slots) :
    r=Rule5ClosedSource.source (ordinarySpec mode base) (fun _ _ _=>0) T S a b q := by
  cases h with
  | refused empty => simp only [Rule5ClosedSource.source,dispatchSource,empty]
  | selected found execution =>
    have hv:=SourceRule5SelectedV3.selected_source_fields sound execution
    simp only [Rule5ClosedSource.source,dispatchSource,found,finish,hv]

def answerView (r : Charged Rule5OrdinaryDispatch.Result) : Charged (Option F) :=
  ⟨match r.value with | .answered answer=>answer | _=>none,r.work+2⟩

theorem dispatch_answer_source
    (sound : ∀ T S b a,OrdExec T S b a→a=base T S b)
    (h : DispatchExec OrdExec mode T S a b q k r slots) :
    answerView r=Rule5ClosedSource.rule5AnswerSource (ordinarySpec mode base) (fun _ _ _=>0) T S a b q := by
  simp only [answerView,Rule5ClosedSource.rule5AnswerSource,←dispatch_source_fields sound h]

theorem admitted_source_fields
    (sound : ∀ T S b a,OrdExec T S b a→a=OrdinaryDispatch.FastOrdinary.solve b T S)
    (h : DispatchExec OrdExec (.cutoff q) T S c.a c.b q k r slots) :
    answerView r=Rule5ClosedSource.admittedRouteSource (fun _ _ _=>0) T S c q := by
  have hv:=dispatch_answer_source (base:=fun T S b=>OrdinaryDispatch.FastOrdinary.solve b T S) sound h
  rw [cutoff_spec] at hv
  simpa only [Rule5ClosedSource.admittedRouteSource,Rule5ClosedSource.actualRule5Source,Rule5ClosedSource.actualCallback] using hv

theorem dispatch_slots_realize (h : DispatchExec OrdExec mode T S a b q k r slots) :
    ∀ s∈slots,SlotRealizes OrdExec mode s := by
  cases h with
  | refused empty => simp
  | selected found execution => exact SourceRule5SelectedV3.selected_slots_realize execution

theorem dispatch_exists
    (total : ∀ T S b,enabled mode b=true→∃ a,OrdExec T S b a)
    (T S : Tree) (a b q k : Nat) : ∃ r slots,DispatchExec OrdExec mode T S a b q k r slots := by
  cases hp:(finalMeter checkFee T S a b).value with
  | none => exact ⟨_,_,DispatchExec.refused hp⟩
  | some z =>
    obtain ⟨r,slots,execution⟩:=SourceRule5SelectedV3.selected_exists total T S a b q k z
    exact ⟨_,_,DispatchExec.selected hp execution⟩
end SourceRule5DispatchV3
