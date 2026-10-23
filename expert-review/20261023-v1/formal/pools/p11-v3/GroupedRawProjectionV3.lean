import GroupedRetainedTraceV3

namespace SourceGroupedRetainsV3
open RMAF Universal233
theorem answer_eq {a b : BothBadGrouped.OutputResult} (h : OutputRetains a b) :
    a.answer?=b.answer? := by
  cases a <;> cases b <;> simp only [OutputRetains,BothBadGrouped.OutputResult.answer?] at h ⊢
  all_goals first | contradiction | rfl | trivial | rw [h.1]
end SourceGroupedRetainsV3

namespace SourceGroupRawV3
open RMAF Universal233 WholeSourceWork CoreWork SourceForestV3 PaidQueries
open OrdinaryDispatch.Hard2SourceWork SourceGroupedRetainsV3

theorem schedule_retained (actual : GenericForest.FrontierWork.Ordinary)
    (q : Nat) (js : List (Job GroupedFullQuery.Problem F)) :
    (literalScheduleSource (groupCallbackMeter actual) q js).value.value=
      (meterSchedule (GroupedFullQuery.callback actual) (fun _ _=>0) q js).value ∧
    (literalScheduleSource (groupCallbackMeter actual) q js).value.queries=
      (meterSchedule (GroupedFullQuery.callback actual) (fun _ _=>0) q js).queries := by
  have hf:(fun p b=>(groupCallbackMeter actual p b).value)=GroupedFullQuery.callback actual := by
    funext p b
    exact groupCallbackMeter_value actual p b
  have hv:=SourceLiteralSchedulerRawV3.schedule_retained (groupCallbackMeter actual) q js
  rw [hf] at hv
  exact hv

theorem output_retains (actual : GenericForest.FrontierWork.Ordinary)
    (T S : Tree) (A B C : List Nat) (q : Nat) (o : CoreProgram.Output) :
    OutputRetains (groupRunOutputLocalSource actual T S A B C q o).value
      (BothBadGrouped.runOutput actual T S A B C q o) := by
  simp only [groupRunOutputLocalSource,groupJobsForMeter_value,BothBadGrouped.runOutput]
  by_cases paid:o.sourceCuts.length≤q
  · simp only [paid,↓reduceIte]
    cases hj:BothBadGrouped.jobsFor T S A B C o with
    | none => trivial
    | some js => exact schedule_retained actual (q-o.sourceCuts.length) js
  · simp only [paid,↓reduceIte]
    trivial

theorem output_answer_value (r : BothBadGrouped.OutputResult) :
    (groupOutputAnswerMeter r).value=r.answer? := by
  cases r <;> simp only [groupOutputAnswerMeter,SourceOrdinaryMafRawV3.flatten_value,
    BothBadGrouped.OutputResult.answer?]
  all_goals rfl

theorem evaluate_value (actual : GenericForest.FrontierWork.Ordinary)
    (T S : Tree) (A B C : List Nat) (q : Nat) (os : List CoreProgram.Output) :
    (groupEvaluateLocalSource actual T S A B C q os).value=BothBadGrouped.evaluate actual T S A B C q os := by
  induction os with
  | nil => rfl
  | cons o os ih =>
    have hr:=output_retains actual T S A B C q o
    have ha:=SourceGroupedRetainsV3.answer_eq hr
    have ht:=SourceGroupedRetainsV3.trace_eq hr
    simp only [groupEvaluateLocalSource,BothBadGrouped.evaluate,output_answer_value,ha,ht,ih]

theorem pair_value (actual : GenericForest.FrontierWork.Ordinary)
    (T S : Tree) (A B C : List Nat) (edge : Vertex×Vertex) (q : Nat) :
    (groupPairLocalSource actual T S A B C edge q).value=
      BothBadGrouped.executePair actual T S A B C edge q := by
  simp only [groupPairLocalSource,pairDescendantsMeter_value,bothBadOutputsMeter_value,evaluate_value,
    SourceBestRawV3.value,forestLengthMeter_value,groupedAcceptedMeter_value,BothBadGrouped.executePair]
end SourceGroupRawV3

namespace SourceGroupPairV3
open RMAF Universal233 SourceForestV3 SourceCouplingV2
open SourceDisjointV2 (ordinarySpec)
variable {OrdExec : Tree→Tree→Nat→Option F→Prop} {mode : Mode}
  {base : Tree→Tree→Nat→Option F} {T S : Tree} {A B C : List Nat}
theorem pair_raw_execution
    (sound : ∀ T S b a,OrdExec T S b a→a=base T S b)
    (h : PairExec OrdExec mode T S A B C edge q k r debits slots) :
    r.value=BothBadGrouped.executePair (ordinarySpec mode base) T S A B C edge q := by
  rw [pair_source_fields sound h,SourceGroupRawV3.pair_value]
end SourceGroupPairV3

namespace SourceBadPairV3
open RMAF Universal233 SourceForestV3 SourceCouplingV2
open GenericForest.CheckCorrespondence OrdinaryDispatch.Hard2SourceWork
open SourceDisjointV2 (ordinarySpec)
variable {OrdExec : Tree→Tree→Nat→Option F→Prop} {mode : Mode}
  {base : Tree→Tree→Nat→Option F} {T S : Tree} {A B C : List Nat}
theorem bad_raw_execution
    (sound : ∀ T S b a,OrdExec T S b a→a=base T S b)
    (h : LocalExec OrdExec mode T S A B C edge q k r debits slots) :
    r.value=OrdinaryDispatch.Hard2Dispatcher.badPair (ordinarySpec mode base) T S A B C edge q := by
  cases h with
  | agrees good execution =>
    rw [meterRestrictionAgrees_value] at good
    have hv:=SourceBothBadPairV3.pair_raw_execution sound execution
    simp only [agreesReturn,OrdinaryDispatch.Hard2Dispatcher.badPair,good,↓reduceIte,hv]
  | grouped bad execution =>
    rw [meterRestrictionAgrees_value] at bad
    have hv:=SourceGroupPairV3.pair_raw_execution sound execution
    simp only [groupedReturn,OrdinaryDispatch.Hard2Dispatcher.badPair,bad,Bool.false_eq_true,↓reduceIte,
      OrdinaryDispatch.Hard2Dispatcher.groupedExecution,groupCalls,hv]
end SourceBadPairV3
