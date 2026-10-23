import QuerySpecification

namespace Universal233.PaidQueries

def badSlots : List (Job P A) → Nat
  | [] => 0
  | .resolved _ c _ :: js => (if c=0 then 0 else 1) + badSlots js
  | .hard _ :: js => 1 + badSlots js

theorem bad_le_known_pending (js : List (Job P A)) :
    badSlots js ≤ knownCost js + pending js := by
  induction js with
  | nil => simp [badSlots,knownCost,pending]
  | cons j js ih =>
    cases j with
    | hard p => simp only [badSlots,knownCost,pending]; omega
    | resolved p c a =>
      simp only [badSlots,knownCost,pending]
      split <;> omega

theorem run_trace (solve : P → Nat → Option (Nat × A)) (b : Nat)
    (js : List (Job P A)) :
    (run solve b js).calls.length ≤ pending js ∧
    (∀ k ∈ (run solve b js).calls, k=b) ∧
    (run solve b js).visits ≤ js.length := by
  induction js with
  | nil => simp [run,pending]
  | cons j js ih =>
    cases j with
    | resolved p c a => simpa [run,pending] using ih
    | hard p =>
      cases he : solve p b with
      | none => simp [run,he,pending]
      | some x =>
        simp only [run,he,List.length_cons,pending]
        refine ⟨by omega,?_,by omega⟩
        intro k hk
        rcases List.mem_cons.1 hk with h | h
        · exact h
        · exact ih.2.1 k h

theorem run_complete_trace (solve : P → Nat → Option (Nat × A)) (b : Nat)
    (js : List (Job P A)) (xs : List (Nat × A))
    (h : (run solve b js).answers = some xs) :
    (run solve b js).calls.length = pending js ∧
      (run solve b js).visits = js.length := by
  induction js generalizing xs with
  | nil => simp [run,pending]
  | cons j js ih =>
    cases j with
    | resolved p c a =>
      cases he : (run solve b js).answers with
      | none => simp [run,he] at h
      | some ys =>
        have ht := ih ys he
        simpa [run,pending] using ht
    | hard p =>
      cases he : solve p b with
      | none => simp [run,he] at h
      | some x =>
        cases ht : (run solve b js).answers with
        | none => simp [run,he,ht] at h
        | some ys =>
          have hi := ih ys ht
          simp only [run,he,pending,List.length_cons]
          omega

theorem schedule_pruned (solve : P → Nat → Option (Nat × A)) (q : Nat)
    (js : List (Job P A)) (h : q < knownCost js + 2*pending js) :
    schedule solve q js = ⟨none,[],0⟩ := by simp [schedule,h]

theorem schedule_trace (solve : P → Nat → Option (Nat × A)) (q : Nat)
    (js : List (Job P A)) :
    (schedule solve q js).calls.length ≤ pending js ∧
    (∀ k ∈ (schedule solve q js).calls, k=allocated q js) ∧
    (schedule solve q js).visits ≤ js.length := by
  unfold schedule
  split
  · simp
  · exact run_trace solve (allocated q js) js

theorem allocation_paid_identity (q : Nat) (js : List (Job P A))
    (h : knownCost js + 2*pending js ≤ q) :
    allocated q js + knownCost js + 2*(pending js-1) = q := by
  simp only [allocated]
  omega

/-- The unit comes from OTHER slots. A sole hard slot with no known cost is
    deliberately excluded by the at-least-two-bad hypothesis. -/
theorem every_query_loses_unit (solve : P → Nat → Option (Nat × A)) (q : Nat)
    (js : List (Job P A)) (hbad : 2 ≤ badSlots js)
    (k : Nat) (hk : k ∈ (schedule solve q js).calls) : k+1 ≤ q := by
  have ht := schedule_trace solve q js
  have he := ht.2.1 k hk
  have hb := bad_le_known_pending js
  by_cases hprune : q < knownCost js + 2*pending js
  · have hz := schedule_pruned solve q js hprune
    rw [hz] at hk
    simp at hk
  · have hi := allocation_paid_identity q js (by omega)
    have hn : 0 < pending js := by
      have hc : 0 < (schedule solve q js).calls.length := List.length_pos_iff.2 (List.ne_nil_of_mem hk)
      omega
    omega

theorem sole_hard_no_discount (p : P) (q : Nat) :
    allocated q ([Job.hard p] : List (Job P A)) = q := by simp [allocated,knownCost,pending]

theorem one_hard_other_cost (js : List (Job P A)) (hbad : 2 ≤ badSlots js)
    (hp : pending js=1) : 1 ≤ knownCost js := by
  have h := bad_le_known_pending js
  omega

theorem multi_hard_paid_loss (solve : P → Nat → Option (Nat × A)) (q : Nat)
    (js : List (Job P A)) (_hp : 2 ≤ pending js)
    (k : Nat) (hk : k ∈ (schedule solve q js).calls) :
    k + 2*(pending js-1) ≤ q := by
  have he := (schedule_trace solve q js).2.1 k hk
  by_cases hprune : q < knownCost js + 2*pending js
  · rw [schedule_pruned solve q js hprune] at hk
    simp at hk
  · have hi := allocation_paid_identity q js (by omega)
    omega
end Universal233.PaidQueries
