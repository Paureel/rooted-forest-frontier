import PaidCaseRawProjectionV3

namespace SourceRule5CanonicalV3
open RMAF Universal233 OrdinaryCommonSplit.Caller HardParent

theorem paid_finish_value (d : Setup) (q : Nat) (FY FN : Forest)
    (actual : Tree→Tree→Nat→Option Forest) :
    runPaid d q FY FN actual=Rule5ActualTrace.finishPaid d q FY FN
      ((paidJobs d q).map (fun j=>actual j.T j.S j.budget)) := rfl

theorem common_trace_value (actual : Rule5OrdinaryDispatch.Ordinary)
    (T S : Tree) (a b : Nat) (d : Rule5FinalClassification.BadSelection) (q : Nat) :
    (Rule5ActualTrace.commonTrace actual T S a b d q).value=
      Rule5CommonSelector.runCommon T S a b d q actual := by
  simp only [Rule5ActualTrace.commonTrace,Rule5CommonSelector.runCommon,OrdinaryCommonSplit.Source.runSource]
  cases hs:OrdinaryCommonSplit.Source.buildSetup T S (subtreeLabels S d.badArc)
      (Rule5CommonSelector.outsideLabels S a b d) d.badArc with
  | none => rfl
  | some setup =>
    simp only [Option.bind_some,runGuarded]
    cases hp:DepthOne.pretest01 setup.ty setup.sy with
    | refused => rfl
    | rejected => rfl
    | found pair =>
      cases pair with
      | none => rfl
      | some p =>
        simp only [runWithOutside]
        cases outsideReply setup (DepthOne.forest setup.sy (some p)) <;> rfl

theorem selected_trace_value (actual : Rule5OrdinaryDispatch.Ordinary)
    (T S : Tree) (a b q : Nat) (z : Rule5FinalClassification.FinalSelection) :
    (Rule5ActualTrace.selectedTrace actual T S a b q z).value=
      Rule5OrdinaryDispatch.runSelected actual T S a b q z := by
  cases z with
  | «prefix» s => simp only [Rule5ActualTrace.selectedTrace,Rule5OrdinaryDispatch.runSelected,forest_jobs_value]
  | remaining d branch =>
    cases branch with
    | first u v => simp only [Rule5ActualTrace.selectedTrace,Rule5OrdinaryDispatch.runSelected,forest_jobs_value]
    | third u v => simp only [Rule5ActualTrace.selectedTrace,Rule5OrdinaryDispatch.runSelected,forest_jobs_value]
    | one x =>
      simp only [Rule5ActualTrace.selectedTrace,Rule5OrdinaryDispatch.runSelected,common_trace_value,
        Rule5CommonOrdinary.runSelectedCommon]
    | second u v =>
      simp only [Rule5ActualTrace.selectedTrace,Rule5OrdinaryDispatch.runSelected,Rule5PaidOrdinary.solveSelected]
      cases Rule5PaidSelector.buildSelected T S a b <;> simp only [paid_best_value]
      all_goals rfl

theorem dispatch_trace_value (actual : Rule5OrdinaryDispatch.Ordinary)
    (T S : Tree) (a b q : Nat) :
    (Rule5ActualTrace.dispatchTrace actual T S a b q).value=Rule5OrdinaryDispatch.dispatch actual T S a b q := by
  simp only [Rule5ActualTrace.dispatchTrace,Rule5OrdinaryDispatch.dispatch]
  cases Rule5FinalClassification.selectFinal T S a b <;> simp only [selected_trace_value]
  all_goals rfl

theorem answer_trace_value (actual : Rule5OrdinaryDispatch.Ordinary)
    (T S : Tree) (a b q : Nat) :
    Rule5ActualTrace.answer (Rule5ActualTrace.dispatchTrace actual T S a b q)=
      OrdinaryDispatch.Hard2Dispatcher.rule5Answer actual T S a b q := by
  simp only [Rule5ActualTrace.answer,dispatch_trace_value,OrdinaryDispatch.Hard2Dispatcher.rule5Answer]
  rfl
end SourceRule5CanonicalV3

namespace SourceRule5DispatchV3
open RMAF Universal233 SourceForestV3 SourceCouplingV2
open SourceDisjointV2 (ordinarySpec)
variable {OrdExec : Tree→Tree→Nat→Option F→Prop} {mode : Mode}
  {base : Tree→Tree→Nat→Option F} {T S : Tree}
theorem dispatch_canonical_value
    (sound : ∀ T S b a,OrdExec T S b a→a=base T S b)
    (h : DispatchExec OrdExec mode T S a b q k r slots) :
    (answerView r).value=OrdinaryDispatch.Hard2Dispatcher.rule5Answer (ordinarySpec mode base) T S a b q := by
  rw [(dispatch_answer_actual_trace sound h).1,SourceRule5CanonicalV3.answer_trace_value]
end SourceRule5DispatchV3
