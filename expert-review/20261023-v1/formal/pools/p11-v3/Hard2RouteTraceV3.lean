import Rule5CanonicalRawValueV3

namespace SourceHard2TraceV3
open RMAF Universal233 SourceForestV3
open OrdinaryDispatch.Hard2SourceWork OrdinaryDispatch.WorkIntegration
open SourcePendantValuesV3 SourceRule4ValuesV3 GenericForest.CheckCorrespondence

-- Mathematical recorded view only; the concrete execution order is carried by the owned graphs.
def routeTrace (actual : GenericForest.FrontierWork.Ordinary) (T S : Tree)
    (c : CherryBranching.Candidate) (q : Nat) : Hard2Route→Hard2Receipt
  | .refused=>⟨none,[]⟩
  | .direct a=>⟨a,[]⟩
  | .admittedRule5=>
    let r:=Rule5ActualTrace.dispatchTrace actual T S c.a c.b q
    ⟨Rule5ActualTrace.answer r,Rule5ActualTrace.queries actual r.calls⟩
  | .disjointPaid=>
    let r:=OrdinaryDispatch.Hard2Trace.disjointExecution actual T S c.a c.b q
    ⟨r.answer,forestQueries actual r.calls⟩
  | .paid out=>
    let r:=OrdinaryDispatch.Hard2Combine.combine actual T S c.a c.b q
      (OrdinaryDispatch.Hard2Dispatcher.paidCase actual T S c q out)
    ⟨r.answer,forestQueries actual r.calls⟩

theorem frontend_trace_cases (actual : GenericForest.FrontierWork.Ordinary)
    (T S : Tree) (c d : CherryBranching.Candidate) (q : Nat) :
    routeTrace actual T S c q (hard2FrontMeter T S c q).value=hard2Trace actual T S c d q := by
  simp only [hard2FrontMeter,runHard2Meter_value,SourcePendantValuesV3.partition_value,all_value,filter_value,
    meterRestrictionAgrees_value,hard2Trace]
  cases hg:Hard2Overlap.runHard2 T S c with
  | none => rfl
  | some out =>
    cases out <;> try rfl
    by_cases good:(CherryBranching.pendantPartition S c.a c.b).all (restrictionAgrees T S)=true
    · simp only [good,↓reduceIte,routeTrace]
    · simp only [good,Bool.false_eq_true,↓reduceIte]
      by_cases two:((CherryBranching.pendantPartition S c.a c.b).filter (restrictionAgrees T S)).length=2
      · simp only [two,↓reduceIte,routeTrace]
      · simp only [two,↓reduceIte,routeTrace]
end SourceHard2TraceV3
