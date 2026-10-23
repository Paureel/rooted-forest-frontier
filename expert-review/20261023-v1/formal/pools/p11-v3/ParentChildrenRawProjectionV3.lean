import GoodPairRawProjectionV3

namespace SourceForestV3
open RMAF Universal233 Universal233.CherryBranching
open OrdinaryDispatch.WorkRecursion SourceCouplingV2
open SourceDisjointV2 (ordinarySpec)

theorem parent_child_answers (actual : GenericForest.FrontierWork.Ordinary)
    (T : Tree) (q : Nat) (cs : List Child) :
    (Rule5OrdinaryDispatch.forestJobs T q cs).filterMap
      (fun j=>GenericForest.solve actual j.target j.sources j.residual)=
      OrdinaryDispatch.childAnswers actual T q cs := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    simp only [Rule5OrdinaryDispatch.forestJobs,OrdinaryDispatch.childAnswers] at ih ⊢
    simp only [List.filterMap_cons,Rule5OrdinaryDispatch.jobFor,childCall]
    cases he:remaining q c with
    | none => simpa only [he,Option.map_none,Option.bind_none] using ih
    | some b =>
      simp only [he,Option.map_some,Option.bind_some,List.filterMap_cons,OrdinaryDispatch.forestChild]
      rw [ih]

theorem children_trace_parent_value (actual : GenericForest.FrontierWork.Ordinary)
    (T right : Tree) (q : Nat) (cs : List Child) :
    (childrenTrace actual T right q cs).value=OrdinaryDispatch.runChildren actual T right q cs := by
  simp only [childrenTrace,Rule5ActualTrace.runForestJobs,parent_child_answers,
    OrdinaryDispatch.runChildren,OrdinaryDispatch.ordinaryAccepted,Rule5OrdinaryDispatch.accepted]
  rfl

variable {OrdExec : Tree→Tree→Nat→Option F→Prop} {mode : Mode}
  {base : Tree→Tree→Nat→Option F}

theorem children_parent_raw
    (sound : ∀ T S b a,OrdExec T S b a→a=base T S b)
    (h : ChildrenExec OrdExec mode T q k cs r debits slots) (right : Tree) :
    (SourceChildrenV2.finishSource T right q r debits).value=
      OrdinaryDispatch.runChildren (ordinarySpec mode base) T right q cs := by
  rw [(children_actual_trace sound h right).1,children_trace_parent_value]
end SourceForestV3

namespace SourceUnitCombineV3
open RMAF Universal233 SourceForestV3 SourceCouplingV2
open OrdinaryDispatch.Hard2Combine SourceHard2ValuesV3
open SourceDisjointV2 (ordinarySpec)
variable {OrdExec : Tree→Tree→Nat→Option F→Prop} {mode : Mode}
  {base : Tree→Tree→Nat→Option F} {T S : Tree}

theorem combine_raw_execution
    (sound : ∀ T S b a,OrdExec T S b a→a=base T S b)
    (h : CombineExec OrdExec mode T S a b q paid k r slots) :
    r.value=combine (ordinarySpec mode base) T S a b q paid := by
  cases h with
  | run children =>
    have hv:=children_parent_raw sound children S
    rw [unit_children_value] at hv
    simp only [finish,choose_value,unit_calls_value,combine,hv]
end SourceUnitCombineV3
