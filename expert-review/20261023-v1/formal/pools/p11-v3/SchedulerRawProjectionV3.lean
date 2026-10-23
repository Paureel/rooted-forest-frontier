import FullOutputsRawProjectionV3

namespace SourceSchedulerRawV3
open RMAF Universal233 WholeSourceWork PaidQueries OrdinaryDispatch.Hard2SourceWork

theorem known_value {P A : Type} (js : List (Job P A)) : (knownCostMeter js).value=knownCost js := by
  induction js with
  | nil => rfl
  | cons j js ih => cases j <;> simp only [knownCostMeter,knownCost,ih]
theorem pending_value {P A : Type} (js : List (Job P A)) : (pendingMeter js).value=pending js := by
  induction js with
  | nil => rfl
  | cons j js ih => cases j <;> simp only [pendingMeter,pending,ih]
theorem allocated_value {P A : Type} (q : Nat) (js : List (Job P A)) :
    (allocatedMeter q js).value=allocated q js := by
  simp only [allocatedMeter,allocated,known_value,pending_value]
theorem answer_cost_value {A : Type} (xs : List (Nat×A)) : (answerCostMeter xs).value=answerCost xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [answerCostMeter,answerCost,List.map_cons,List.sum_cons,ih]
theorem accept_value {A : Type} (q : Nat) (a : Option (List (Nat×A))) :
    (acceptAnswersMeter q a).value=a.bind (fun xs=>if answerCost xs≤q then some xs else none) := by
  cases a <;> simp only [acceptAnswersMeter,answer_cost_value,Option.bind_none,Option.bind_some]

-- Compare retained fields only: literal32 and raw5/8 work words differ.
theorem run_retained {P A : Type} (f : P→Nat→Charged (Option (Nat×A)))
    (charge : P→Nat→Nat) (b : Nat) (js : List (Job P A)) :
    (runSourceMeter f b js).value=(meterRun (fun p b=>(f p b).value) charge b js).value ∧
    (runSourceMeter f b js).queries=(meterRun (fun p b=>(f p b).value) charge b js).queries := by
  induction js with
  | nil => constructor <;> first | rfl | trivial
  | cons j js ih =>
    cases j with
    | resolved p c a =>
      simp only [runSourceMeter,meterRun,ih.1,ih.2]
      constructor <;> first | rfl | trivial
    | hard p =>
      cases he:(f p b).value <;> simp only [runSourceMeter,meterRun,he,ih.1,ih.2]
      all_goals constructor <;> first | rfl | trivial

theorem schedule_retained {P A : Type} (f : P→Nat→Charged (Option (Nat×A)))
    (charge : P→Nat→Nat) (q : Nat) (js : List (Job P A)) :
    (scheduleSourceMeter f q js).value=(meterSchedule (fun p b=>(f p b).value) charge q js).value ∧
    (scheduleSourceMeter f q js).queries=(meterSchedule (fun p b=>(f p b).value) charge q js).queries := by
  simp only [scheduleSourceMeter,meterSchedule,known_value,pending_value,allocated_value,accept_value]
  by_cases low:q<knownCost js+2*pending js
  · simp only [low,↓reduceIte]
    constructor <;> first | rfl | trivial
  · simp only [low,↓reduceIte,(run_retained f charge (allocated q js) js).1,
      (run_retained f charge (allocated q js) js).2]
    constructor <;> first | rfl | trivial
end SourceSchedulerRawV3
