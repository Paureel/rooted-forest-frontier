import ForestDisjoint
namespace GenericForest.LocalIH
open RMAF ForestState Universal233 Universal233.PaidQueries

theorem run_congr {P A : Type} (f g : P → Nat → Option (Nat × A))
    (b : Nat) (js : List (Job P A)) (h : ∀ p, f p b = g p b) :
    run f b js = run g b js := by
  induction js with
  | nil => rfl
  | cons j js ih =>
    cases j with
    | resolved p c a => simp only [run, ih]
    | hard p => simp only [run, h p, ih]

theorem schedule_congr {P A : Type} (f g : P → Nat → Option (Nat × A))
    (q : Nat) (js : List (Job P A))
    (h : ∀ p b, b ≤ q → f p b = g p b) :
    schedule f q js = schedule g q js := by
  have hb : allocated q js ≤ q := by simp only [allocated]; omega
  unfold schedule
  rw [run_congr f g (allocated q js) js (fun p => h p _ hb)]

theorem disjointSolve_congr
    (f g : Tree → Tree → Nat → Option Forest) (q : Nat)
    (h : ∀ t s b, b ≤ q → f t s b = g t s b)
    (t : Tree) (ss : List Tree) :
    disjointSolve t ss f q = disjointSolve t ss g q := by
  unfold disjointSolve disjointAttempt
  cases hj : jobs t ss with
  | none => rfl
  | some js =>
    have hs := schedule_congr
      (fun p b => (f p.1 p.2 b).map (fun F => (F.length-1,F)))
      (fun p b => (g p.1 p.2 b).map (fun F => (F.length-1,F))) q js
      (fun p b hb => congrArg (Option.map (fun F : Forest => (F.length-1,F))) (h p.1 p.2 b hb))
    simp only [Option.map_some, hs]

/-- Actual executable callback locality. No callback correctness, state
properness, mathematical completion, or graph premise is needed. -/
theorem solve_congr_budget
    (f g : Tree → Tree → Nat → Option Forest) (q : Nat)
    (h : ∀ t s b, b ≤ q → f t s b = g t s b)
    (T : Option Tree) (ss : List Tree) :
    solve f T ss q = solve g T ss q := by
  induction q using Nat.strongRecOn generalizing T ss with
  | ind q ih =>
    rw [solve.eq_def, solve.eq_def]
    split
    · split
      · rfl
      · split
        · rfl
        · have hq : ∀ t s, f t s q = g t s q := fun t s => h t s q (Nat.le_refl _)
          simp only [hq]
        ·
          split
          · exact disjointSolve_congr f g q h _ _
          · dsimp only
            apply congrArg (best List.length (accepted _ _ q))
            apply congrArg (List.filterMap · _)
            funext io
            split
            · rename_i hd
              apply ih (q-io.2.sourceCuts.length) (by omega)
              intro u v k hk
              exact h u v k (by omega)
            · rfl
    · rfl
end GenericForest.LocalIH
