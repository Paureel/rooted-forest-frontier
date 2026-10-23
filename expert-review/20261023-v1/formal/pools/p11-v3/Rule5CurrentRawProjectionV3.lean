import Rule5ArmRawProjectionV3

namespace SourceRule5CurrentV3
open RMAF Universal233 WholeSourceWork SourceForestV3
open Universal233.Rule5ExecutionSource
open GenericForest GenericForest.FrontierWork
open SourceCouplingV2 (Mode)
open SourceDisjointV2 (ordinarySpec)
variable {OrdExec : Tree→Tree→Nat→Option F→Prop} {mode : Mode}
  {base : Tree→Tree→Nat→Option F}

-- forest_pretest_value is the second narrowly audited pure primitive interface used.
theorem current_raw_projection
    (sound : ∀ T S b a,OrdExec T S b a→a=base T S b)
    (h : CurrentExec OrdExec mode T ss r k result slots) :
    result.value=Rule5PaidOrdinary.currentQuery (ordinarySpec mode base) T ss r ∧
    result.ordinaryCalls=Rule5ActualTrace.currentFrontier (ordinarySpec mode base) T ss r := by
  rw [current_source_fields sound h]
  simp only [currentQueryMeter,Universal233.Rule5ExecutionSource.forest_pretest_value,
    Rule5PaidOrdinary.currentQuery,Rule5ActualTrace.currentFrontier]
  cases hp:ForestPretest01.pretest01 T ss with
  | refused => constructor <;> first | rfl | trivial
  | found F0 => constructor <;> first | rfl | trivial
  | rejected =>
    by_cases low:r≤1
    · simp only [low,↓reduceIte]
      constructor <;> first | rfl | trivial
    · simp only [low,↓reduceIte]
      constructor <;> first | rfl | trivial
end SourceRule5CurrentV3

namespace SourceRule5PaidRequestV3
open RMAF Universal233 WholeSourceWork SourceForestV3
open Universal233.Rule5ExecutionSource Universal233.Rule5PaidSelector
open SourceCouplingV2 (Mode)
open SourceDisjointV2 (ordinarySpec)
variable {OrdExec : Tree→Tree→Nat→Option F→Prop} {mode : Mode}
  {base : Tree→Tree→Nat→Option F}

theorem request_raw_projection
    (sound : ∀ T S b a,OrdExec T S b a→a=base T S b)
    (h : RequestExec OrdExec mode j k r slots) :
    r.value=Rule5PaidOrdinary.currentAnswer (ordinarySpec mode base) (some j.target) j.sources j.residual ∧
    r.ordinaryCalls=Rule5ActualTrace.currentFrontier (ordinarySpec mode base) (some j.target) j.sources j.residual := by
  cases h with
  | run execution =>
    have hv:=SourceRule5CurrentV3.current_raw_projection sound execution
    simp only [requestReturn,Rule5PaidOrdinary.currentAnswer,hv.1,hv.2]
    constructor <;> first | rfl | trivial

theorem list_raw_projection
    (sound : ∀ T S b a,OrdExec T S b a→a=base T S b)
    (h : AnswerListExec OrdExec mode k js r slots) :
    r.value=js.filterMap (fun j=>Rule5PaidOrdinary.currentAnswer (ordinarySpec mode base) (some j.target) j.sources j.residual) ∧
    r.ordinaryCalls=js.flatMap (fun j=>Rule5ActualTrace.currentFrontier (ordinarySpec mode base) (some j.target) j.sources j.residual) := by
  induction h with
  | nil => constructor <;> first | rfl | trivial
  | @cons j k a slots js r ss head tail ih =>
    have hv:=request_raw_projection sound head
    constructor
    · simp only [prepend,List.filterMap_cons,←hv.1,←ih.1]
      cases he:a.value <;> simp only [he]
    · simp only [prepend,List.flatMap_cons,hv.2,ih.2]
end SourceRule5PaidRequestV3
