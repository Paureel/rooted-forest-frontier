import Work
import Precontrols

namespace Universal233.PaidQueries.ConsumerControls
open Precontrols

theorem planted_sound (p b c a : Nat) (h : plantedSolver p b=some (c,a)) :
    c=p ∧ p=a := by
  unfold plantedSolver at h
  split at h
  · have hh : p=c ∧ p=a := by simpa using h
    exact ⟨hh.1.symm,hh.2⟩
  · simp at h

theorem planted_complete (p b : Nat) (h : p≤b) : ∃ x, plantedSolver p b=some x := by
  exact ⟨(p,p),by simp [plantedSolver,h]⟩

theorem control_conditional_theorem :
    (∃ xs, (schedule plantedSolver 4 [h 2,h 2]).answers=some xs) ↔
      totalMinimum id ([h 2,h 2] : List (Job Nat Nat))≤4 := by
  apply schedule_accepts_iff id (fun p a => p=a) plantedSolver planted_sound planted_complete
  intro j hj
  have he : j=h 2 := by simpa using hj
  subst j
  simp [h,Planned]

theorem control_failed_total_after_success :
    (run plantedSolver 3 [h 3,h 3]).answers=some [(3,3),(3,3)] ∧
      (schedule plantedSolver 5 [h 3,h 3]).answers=none := by decide

theorem control_actual_problem_dispatch :
    (meterSchedule plantedSolver (fun p b => 100*p+b) 6 [h 2,h 6]).queries=[(2,4),(6,4)] ∧
    (meterSchedule plantedSolver (fun p b => 100*p+b) 6 [h 2,h 6]).recursiveWork=808 := by decide

theorem control_pruned_dispatch :
    (meterSchedule plantedSolver (fun p b => 100*p+b) 3 [h 2,h 2]).queries=[] ∧
    (meterSchedule plantedSolver (fun p b => 100*p+b) 3 [h 2,h 2]).recursiveWork=0 := by decide

theorem control_duplicates_charged :
    (meterSchedule plantedSolver (fun _ _ => 1) 4 [h 2,h 2]).queries=[(2,2),(2,2)] ∧
    (meterSchedule plantedSolver (fun _ _ => 1) 4 [h 2,h 2]).recursiveWork=2 := by decide

theorem control_zero_hard_known_charge :
    (schedule plantedSolver 1 [k 0,k 1]).visits=2 ∧
    (meterSchedule plantedSolver (fun _ _ => 1) 1 [k 0,k 1]).recursiveWork=0 := by decide

theorem control_unit_excludes_sole :
    badSlots ([h 2] : List (Job Nat Nat))=1 ∧ allocated 3 ([h 2] : List (Job Nat Nat))=3 := by decide

theorem control_unit_one_hard :
    badSlots ([k 1,h 2] : List (Job Nat Nat))=2 ∧
      (schedule plantedSolver 3 [k 1,h 2]).calls=[2] := by decide
end Universal233.PaidQueries.ConsumerControls
