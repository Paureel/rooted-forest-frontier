import BothBadRawProjectionV3

namespace SourceLiteralSchedulerRawV3
open RMAF Universal233 WholeSourceWork PaidQueries
open OrdinaryDispatch.Hard2SourceWork SourceSchedulerRawV3

theorem run_retained {P A : Type} (f : P→Nat→Charged (Option (Nat×A)))
    (b : Nat) (js : List (Job P A)) :
    (literalRunSource f b js).value.value=(meterRun (fun p b=>(f p b).value) (fun _ _=>0) b js).value ∧
    (literalRunSource f b js).value.queries=(meterRun (fun p b=>(f p b).value) (fun _ _=>0) b js).queries := by
  induction js with
  | nil => constructor <;> rfl
  | cons j js ih =>
    cases j with
    | resolved p c a =>
      simp only [literalRunSource,meterRun,ih.1,ih.2]
      constructor <;> first | rfl | trivial
    | hard p =>
      cases he:(f p b).value <;> simp only [literalRunSource,meterRun,he,ih.1,ih.2]
      all_goals constructor <;> first | rfl | trivial

theorem schedule_retained {P A : Type} (f : P→Nat→Charged (Option (Nat×A)))
    (q : Nat) (js : List (Job P A)) :
    (literalScheduleSource f q js).value.value=
      (meterSchedule (fun p b=>(f p b).value) (fun _ _=>0) q js).value ∧
    (literalScheduleSource f q js).value.queries=
      (meterSchedule (fun p b=>(f p b).value) (fun _ _=>0) q js).queries := by
  simp only [literalScheduleSource,meterSchedule,known_value,pending_value,allocated_value,accept_value]
  by_cases low:q<knownCost js+2*pending js
  · simp only [low,↓reduceIte]
    constructor <;> first | rfl | trivial
  · simp only [low,↓reduceIte,(run_retained f (allocated q js) js).1,
      (run_retained f (allocated q js) js).2]
    constructor <;> first | rfl | trivial
end SourceLiteralSchedulerRawV3
