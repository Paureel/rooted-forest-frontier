import QueryCaller

namespace Universal233.PaidQueries

def Planned (minimum : P → Nat) (valid : P → A → Prop) : Job P A → Prop
  | .resolved p c a => c = minimum p ∧ valid p a ∧ c ≤ 1
  | .hard p => 2 ≤ minimum p

def totalMinimum (minimum : P → Nat) : List (Job P A) → Nat
  | [] => 0
  | j :: js => minimum j.problem + totalMinimum minimum js

inductive AnswersFor (minimum : P → Nat) (valid : P → A → Prop) :
    List (Job P A) → List (Nat × A) → Prop where
  | nil : AnswersFor minimum valid [] []
  | cons {j : Job P A} {x : Nat × A} {js : List (Job P A)} {xs : List (Nat × A)} :
      (x.1 = minimum j.problem ∧ valid j.problem x.2) →
      AnswersFor minimum valid js xs → AnswersFor minimum valid (j::js) (x::xs)

theorem planned_tail (minimum : P → Nat) (valid : P → A → Prop)
    (j : Job P A) (js : List (Job P A))
    (h : ∀ k ∈ j::js, Planned minimum valid k) : ∀ k ∈ js, Planned minimum valid k := by
  intro k hk
  exact h k (by simp [hk])

theorem total_lower (minimum : P → Nat) (valid : P → A → Prop)
    (js : List (Job P A)) (h : ∀ j ∈ js, Planned minimum valid j) :
    knownCost js + 2*pending js ≤ totalMinimum minimum js := by
  induction js with
  | nil => simp [knownCost,pending,totalMinimum]
  | cons j js ih =>
    have ht := ih (planned_tail minimum valid j js h)
    have hh := h j (by simp)
    cases j with
    | resolved p c a =>
      simp only [Planned] at hh
      simp only [knownCost,pending,totalMinimum,Job.problem]
      omega
    | hard p =>
      simp only [Planned] at hh
      simp only [knownCost,pending,totalMinimum,Job.problem]
      omega

theorem hard_pending_positive (p : P) (js : List (Job P A))
    (h : Job.hard p ∈ js) : 0 < pending js := by
  induction js with
  | nil => simp at h
  | cons j js ih =>
    rcases List.mem_cons.1 h with he | ht
    · subst j; simp only [pending]; omega
    · cases j <;> simp only [pending] <;> have := ih ht <;> omega

theorem other_lower (minimum : P → Nat) (valid : P → A → Prop)
    (js : List (Job P A)) (h : ∀ j ∈ js, Planned minimum valid j)
    (p : P) (hp : Job.hard p ∈ js) :
    minimum p + knownCost js + 2*(pending js-1) ≤ totalMinimum minimum js := by
  induction js with
  | nil => simp at hp
  | cons j js ih =>
    have ht := planned_tail minimum valid j js h
    have hh := h j (by simp)
    cases j with
    | resolved u c a =>
      have hm : Job.hard p ∈ js := by simpa using hp
      have hi := ih ht hm
      simp only [Planned] at hh
      simp only [knownCost,pending,totalMinimum,Job.problem]
      omega
    | hard u =>
      rcases List.mem_cons.1 hp with he | hm
      · have heu : p = u := by cases he; rfl
        subst u
        have hl := total_lower minimum valid js ht
        simp only [knownCost,pending,totalMinimum,Job.problem]
        omega
      · have hi := ih ht hm
        have hn := hard_pending_positive p js hm
        simp only [Planned] at hh
        simp only [knownCost,pending,totalMinimum,Job.problem]
        omega

theorem feasible_allocation (minimum : P → Nat) (valid : P → A → Prop)
    (js : List (Job P A)) (h : ∀ j ∈ js, Planned minimum valid j)
    (q : Nat) (hq : totalMinimum minimum js ≤ q)
    (p : P) (hp : Job.hard p ∈ js) : minimum p ≤ allocated q js := by
  have hl := other_lower minimum valid js h p hp
  simp only [allocated]
  omega

theorem answers_cost (minimum : P → Nat) (valid : P → A → Prop)
    (js : List (Job P A)) (xs : List (Nat × A)) (h : AnswersFor minimum valid js xs) :
    answerCost xs = totalMinimum minimum js ∧ xs.length = js.length := by
  induction h with
  | nil => simp [answerCost,totalMinimum]
  | @cons j x js xs hj hrest ih =>
    simp only [answerCost,List.map_cons,List.sum_cons,totalMinimum,List.length_cons] at *
    exact ⟨by rw [hj.1,ih.1],by omega⟩

/- The following two hypotheses are the FUTURE exact recursive solver induction
   hypothesis. This package does not construct that solver or assume graph
   coverage, disjoint reconstruction, or a runtime theorem. -/
theorem run_sound (minimum : P → Nat) (valid : P → A → Prop)
    (solve : P → Nat → Option (Nat × A))
    (hs : ∀ p b c a, solve p b = some (c,a) → c = minimum p ∧ valid p a)
    (b : Nat) (js : List (Job P A)) (hp : ∀ j ∈ js, Planned minimum valid j)
    (xs : List (Nat × A)) (hr : (run solve b js).answers = some xs) :
    AnswersFor minimum valid js xs := by
  induction js generalizing xs with
  | nil =>
    have hx : xs = [] := by simpa [run] using hr.symm
    subst xs
    exact AnswersFor.nil
  | cons j js ih =>
    have ht := planned_tail minimum valid j js hp
    cases j with
    | resolved p c a =>
      have hh := hp (.resolved p c a) (by simp)
      cases he : (run solve b js).answers with
      | none => simp [run,he] at hr
      | some ys =>
        have hx : xs = (c,a)::ys := by simpa [run,he] using hr.symm
        subst xs
        exact AnswersFor.cons ⟨hh.1,hh.2.1⟩ (ih ht ys he)
    | hard p =>
      cases he : solve p b with
      | none => simp [run,he] at hr
      | some x =>
        cases x with
        | mk c a =>
          cases htres : (run solve b js).answers with
          | none => simp [run,he,htres] at hr
          | some ys =>
            have hx : xs = (c,a)::ys := by simpa [run,he,htres] using hr.symm
            subst xs
            exact AnswersFor.cons (hs p b c a he) (ih ht ys htres)

theorem run_complete (minimum : P → Nat)
    (solve : P → Nat → Option (Nat × A))
    (hc : ∀ p b, minimum p ≤ b → ∃ x, solve p b = some x)
    (b : Nat) (js : List (Job P A))
    (hf : ∀ p, Job.hard p ∈ js → minimum p ≤ b) :
    ∃ xs, (run solve b js).answers = some xs := by
  induction js with
  | nil => exact ⟨[],rfl⟩
  | cons j js ih =>
    have htail : ∀ p, Job.hard p ∈ js → minimum p ≤ b := by
      intro p hp; exact hf p (by simp [hp])
    obtain ⟨ys,hy⟩ := ih htail
    cases j with
    | resolved p c a => exact ⟨(c,a)::ys,by simp [run,hy]⟩
    | hard p =>
      obtain ⟨x,hx⟩ := hc p b (hf p (by simp))
      exact ⟨x::ys,by simp [run,hx,hy]⟩

theorem schedule_sound (minimum : P → Nat) (valid : P → A → Prop)
    (solve : P → Nat → Option (Nat × A))
    (hs : ∀ p b c a, solve p b = some (c,a) → c = minimum p ∧ valid p a)
    (q : Nat) (js : List (Job P A)) (hp : ∀ j ∈ js, Planned minimum valid j)
    (xs : List (Nat × A)) (hr : (schedule solve q js).answers = some xs) :
    AnswersFor minimum valid js xs ∧ answerCost xs = totalMinimum minimum js ∧
      totalMinimum minimum js ≤ q := by
  unfold schedule at hr
  split at hr
  · simp at hr
  · rename_i hprune
    cases he : (run solve (allocated q js) js).answers with
    | none => simp [he] at hr
    | some ys =>
      by_cases hcost : answerCost ys ≤ q
      · have hx : xs = ys := by simpa [he,hcost] using hr.symm
        subst xs
        have ha := run_sound minimum valid solve hs (allocated q js) js hp ys he
        have hsum := (answers_cost minimum valid js ys ha).1
        exact ⟨ha,hsum,by omega⟩
      · simp [he,hcost] at hr

theorem schedule_complete (minimum : P → Nat) (valid : P → A → Prop)
    (solve : P → Nat → Option (Nat × A))
    (hs : ∀ p b c a, solve p b = some (c,a) → c = minimum p ∧ valid p a)
    (hc : ∀ p b, minimum p ≤ b → ∃ x, solve p b = some x)
    (q : Nat) (js : List (Job P A)) (hp : ∀ j ∈ js, Planned minimum valid j)
    (hq : totalMinimum minimum js ≤ q) :
    ∃ xs, (schedule solve q js).answers = some xs := by
  have hl := total_lower minimum valid js hp
  have hprune : ¬q < knownCost js + 2*pending js := by omega
  have hf := feasible_allocation minimum valid js hp q hq
  obtain ⟨xs,hxs⟩ := run_complete minimum solve hc (allocated q js) js hf
  have ha := run_sound minimum valid solve hs (allocated q js) js hp xs hxs
  have hsum := (answers_cost minimum valid js xs ha).1
  refine ⟨xs,?_⟩
  simp [schedule,hprune,hxs,show answerCost xs ≤ q by omega]

theorem schedule_accepts_iff (minimum : P → Nat) (valid : P → A → Prop)
    (solve : P → Nat → Option (Nat × A))
    (hs : ∀ p b c a, solve p b = some (c,a) → c = minimum p ∧ valid p a)
    (hc : ∀ p b, minimum p ≤ b → ∃ x, solve p b = some x)
    (q : Nat) (js : List (Job P A)) (hp : ∀ j ∈ js, Planned minimum valid j) :
    (∃ xs, (schedule solve q js).answers = some xs) ↔ totalMinimum minimum js ≤ q := by
  constructor
  · rintro ⟨xs,hxs⟩
    exact (schedule_sound minimum valid solve hs q js hp xs hxs).2.2
  · exact schedule_complete minimum valid solve hs hc q js hp
end Universal233.PaidQueries
