import ControlFlowV4
import Hard2Program
open Universal233 PaidQueries
namespace FreshOrdinaryBridge
theorem meter_run_value {P A : Type} (solve : P→Nat→Option (Nat×A))
    (charge : P→Nat→Nat) (b : Nat) (js : List (Job P A)) :
    (meterRun solve charge b js).value=run solve b js := by
  induction js with
  | nil => rfl
  | cons j js ih =>
    cases j with
    | resolved p c a =>
      simp only [meterRun,run]
      rw [ih]
    | hard p =>
      cases he : solve p b with
      | none => simp only [meterRun,run,he]
      | some x =>
        simp only [meterRun,run,he]
        rw [ih]

theorem meter_schedule_value {P A : Type} (solve : P→Nat→Option (Nat×A))
    (charge : P→Nat→Nat) (q : Nat) (js : List (Job P A)) :
    (meterSchedule solve charge q js).value=schedule solve q js := by
  by_cases h : q<knownCost js+2*pending js
  · simp only [meterSchedule,schedule,if_pos h]
  · simp only [meterSchedule,schedule,if_neg h]
    rw [meter_run_value]

theorem meter_queries_budget {P A : Type} (solve : P→Nat→Option (Nat×A))
    (charge : P→Nat→Nat) (b : Nat) (js : List (Job P A)) :
    ∀ ub∈(meterRun solve charge b js).queries, ub.2=b ∧ Job.hard ub.1∈js := by
  induction js with
  | nil =>
    intro ub hub
    exact False.elim (List.not_mem_nil hub)
  | cons j js ih =>
    cases j with
    | resolved p c a =>
      change ∀ ub∈(meterRun solve charge b js).queries, ub.2=b ∧ Job.hard ub.1∈Job.resolved p c a::js
      intro ub hub
      exact ⟨(ih ub hub).1,List.mem_cons_of_mem _ (ih ub hub).2⟩
    | hard p =>
      cases he : solve p b with
      | none =>
        simpa only [meterRun,he,List.mem_singleton,forall_eq,Prod.fst,Prod.snd,List.mem_cons_self,and_self] using True.intro
      | some x =>
        simp only [meterRun,he]
        change ∀ ub∈(p,b)::(meterRun solve charge b js).queries, ub.2=b ∧ Job.hard ub.1∈Job.hard p::js
        intro ub hub
        rcases List.mem_cons.mp hub with rfl|hub
        · exact ⟨rfl,List.mem_cons_self⟩
        · exact ⟨(ih ub hub).1,List.mem_cons_of_mem _ (ih ub hub).2⟩
end FreshOrdinaryBridge

-- Author integration type/axiom reports; proof text above is unchanged apart from recorded import edits.
set_option pp.universes true
#check @FreshOrdinaryBridge.meter_run_value
#print axioms FreshOrdinaryBridge.meter_run_value
#check @FreshOrdinaryBridge.meter_schedule_value
#print axioms FreshOrdinaryBridge.meter_schedule_value
#check @FreshOrdinaryBridge.meter_queries_budget
#print axioms FreshOrdinaryBridge.meter_queries_budget
