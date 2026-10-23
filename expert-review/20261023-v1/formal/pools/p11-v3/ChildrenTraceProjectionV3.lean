import CompleteCommonV3

namespace SourceLocalValuesV3
open RMAF Universal233 Universal233.Rule5SelectedLocalWork

theorem bestLength_value (check : SourceForestV3.F→Rule5PrefixLocalWork.Measured Bool)
    (xs : List SourceForestV3.F) :
    (bestLengthMeter check xs).value=best List.length (fun f=>(check f).value) xs := by
  induction xs with
  | nil => rfl
  | cons f fs ih =>
    simp only [bestLengthMeter,best,ih]
    by_cases hc:(check f).value=true
    · simp only [hc,Bool.false_eq_true,↓reduceIte]
      split <;> rename_i hr <;> simp only [hr]
      all_goals first | rfl | (split <;> rfl)
    · simp only [hc,Bool.false_eq_true,↓reduceIte]

end SourceLocalValuesV3

namespace SourceForestV3
open RMAF Universal233 Universal233.CherryBranching Universal233.Rule5SelectedLocalWork
open GenericForest GenericForest.FrontierWork SourceChildrenV2 SourceCouplingV2
open SourceDisjointV2 (ordinarySpec)
open OrdinaryDispatch.WorkRecursion SourceLocalValuesV3
open CallbackPairingAuthor (indexFrom)

variable {OrdExec : Tree→Tree→Nat→Option SourceForestV3.F→Prop} {mode : Mode}
  {base : Tree→Tree→Nat→Option SourceForestV3.F}

theorem children_values
    (sound : ∀ T S b a,OrdExec T S b a→a=base T S b)
    (h : ChildrenExec OrdExec mode T q k cs r debits slots) :
    r.value=(Rule5OrdinaryDispatch.forestJobs T q cs).filterMap
      (fun j=>GenericForest.solve (ordinarySpec mode base) j.target j.sources j.residual) := by
  induction h with
  | nil => rfl
  | refused over tail ih =>
    simpa only [prependChild,Rule5OrdinaryDispatch.forestJobs,Rule5OrdinaryDispatch.jobFor,
      remaining,over,↓reduceIte,Option.map_none,List.filterMap_cons] using ih
  | returned paid execution tail ih =>
    have hv:=(forest_correspondence sound _ _ _ _ _ execution).1
    simp only [Rule5OrdinaryDispatch.forestJobs] at ih
    simp only [prependChild,Rule5OrdinaryDispatch.forestJobs,Rule5OrdinaryDispatch.jobFor,
      remaining,paid,↓reduceIte,Option.map_some,List.filterMap_cons,←hv,←ih]
    split <;> rename_i he <;> simp only [he]

theorem children_actual_trace
    (sound : ∀ T S b a,OrdExec T S b a→a=base T S b)
    (h : ChildrenExec OrdExec mode T q k cs r debits slots) (right : Tree) :
    (finishSource T right q r debits).value=
      (childrenTrace (ordinarySpec mode base) T right q cs).value ∧
    slots.map (fun s=>(s.index,s.query))=
      indexFrom k (childrenTrace (ordinarySpec mode base) T right q cs).queries := by
  have hv:=children_values sound h
  have hq:=children_index sound h
  constructor
  · simp only [finishSource,finishChildren,childrenTrace,Rule5ActualTrace.runForestJobs,
      SourceLocalValuesV3.bestLength_value,acceptedMeter,Rule5OrdinaryDispatch.accepted,hv]
    rfl
  · exact hq

end SourceForestV3
