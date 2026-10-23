import LocalSlots

namespace Universal233.MafScheduler
open PaidQueries

theorem run_sound_on (minimum : P → Nat) (valid : P → A → Prop)
    (solve : P → Nat → Option (Nat × A)) (Q : List P)
    (hs : ∀ p∈Q, ∀ b c a, solve p b=some (c,a) → c=minimum p ∧ valid p a)
    (b : Nat) (js : List (Job P A)) (hp : ∀ j∈js, Planned minimum valid j)
    (hkeys : ∀ j∈js, j.problem∈Q) (xs : List (Nat × A))
    (hr : (run solve b js).answers=some xs) : AnswersFor minimum valid js xs := by
  induction js generalizing xs with
  | nil =>
    have he : xs=[] := by simpa [run] using hr.symm
    subst xs; exact .nil
  | cons j js ih =>
    have ht := planned_tail minimum valid j js hp
    have hkt : ∀ k∈js, k.problem∈Q := fun k hk => hkeys k (by simp [hk])
    cases j with
    | resolved p c a =>
      cases he : (run solve b js).answers with
      | none => simp [run,he] at hr
      | some ys =>
        have hx : xs=(c,a)::ys := by simpa [run,he] using hr.symm
        subst xs
        have hh := hp (.resolved p c a) (by simp)
        exact .cons ⟨hh.1,hh.2.1⟩ (ih ht hkt ys he)
    | hard p =>
      cases he : solve p b with
      | none => simp [run,he] at hr
      | some x =>
        rcases x with ⟨c,a⟩
        cases hrest : (run solve b js).answers with
        | none => simp [run,he,hrest] at hr
        | some ys =>
          have hx : xs=(c,a)::ys := by simpa [run,he,hrest] using hr.symm
          subst xs
          exact .cons (hs p (hkeys (.hard p) (by simp)) b c a he) (ih ht hkt ys hrest)

theorem run_complete_on (minimum : P → Nat) (solve : P → Nat → Option (Nat × A))
    (Q : List P) (hc : ∀ p∈Q, ∀ b, minimum p≤b → ∃ x, solve p b=some x)
    (b : Nat) (js : List (Job P A)) (hkeys : ∀ j∈js, j.problem∈Q)
    (hf : ∀ p, Job.hard p∈js → minimum p≤b) :
    ∃ xs, (run solve b js).answers=some xs := by
  induction js with
  | nil => exact ⟨[],rfl⟩
  | cons j js ih =>
    obtain ⟨ys,hy⟩ := ih (fun k hk => hkeys k (by simp [hk]))
      (fun p hp => hf p (by simp [hp]))
    cases j with
    | resolved p c a => exact ⟨(c,a)::ys,by simp [run,hy]⟩
    | hard p =>
      obtain ⟨x,hx⟩ := hc p (hkeys (.hard p) (by simp)) b (hf p (by simp))
      exact ⟨x::ys,by simp [run,hx,hy]⟩

theorem schedule_sound_on (minimum : P → Nat) (valid : P → A → Prop)
    (solve : P → Nat → Option (Nat × A)) (Q : List P)
    (hs : ∀ p∈Q, ∀ b c a, solve p b=some (c,a) → c=minimum p ∧ valid p a)
    (q : Nat) (js : List (Job P A)) (hp : ∀ j∈js, Planned minimum valid j)
    (hkeys : ∀ j∈js, j.problem∈Q) (xs : List (Nat × A))
    (hr : (schedule solve q js).answers=some xs) :
    AnswersFor minimum valid js xs ∧ answerCost xs=totalMinimum minimum js ∧
      totalMinimum minimum js≤q := by
  unfold schedule at hr
  split at hr
  · simp at hr
  · cases he : (run solve (allocated q js) js).answers with
    | none => simp [he] at hr
    | some ys =>
      by_cases hc : answerCost ys≤q
      · have hx : xs=ys := by simpa [he,hc] using hr.symm
        subst xs
        have ha := run_sound_on minimum valid solve Q hs (allocated q js) js hp hkeys ys he
        have hsum := (answers_cost minimum valid js ys ha).1
        exact ⟨ha,hsum,by omega⟩
      · simp [he,hc] at hr

theorem schedule_complete_on (minimum : P → Nat) (valid : P → A → Prop)
    (solve : P → Nat → Option (Nat × A)) (Q : List P)
    (hs : ∀ p∈Q, ∀ b c a, solve p b=some (c,a) → c=minimum p ∧ valid p a)
    (hc : ∀ p∈Q, ∀ b, minimum p≤b → ∃ x, solve p b=some x)
    (q : Nat) (js : List (Job P A)) (hp : ∀ j∈js, Planned minimum valid j)
    (hkeys : ∀ j∈js, j.problem∈Q) (hq : totalMinimum minimum js≤q) :
    ∃ xs, (schedule solve q js).answers=some xs := by
  have hl := total_lower minimum valid js hp
  have hprune : ¬q<knownCost js+2*pending js := by omega
  obtain ⟨xs,hxs⟩ := run_complete_on minimum solve Q hc (allocated q js) js hkeys
    (feasible_allocation minimum valid js hp q hq)
  have ha := run_sound_on minimum valid solve Q hs (allocated q js) js hp hkeys xs hxs
  have hsum := (answers_cost minimum valid js xs ha).1
  exact ⟨xs,by simp [schedule,hprune,hxs,show answerCost xs≤q by omega]⟩
end Universal233.MafScheduler
