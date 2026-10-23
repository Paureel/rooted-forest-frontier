import DispatchControls

namespace Universal233.BothBad
open RMAF CoreProgram

theorem checked_sound (T S : Tree) (q : Nat) (o : Option Forest) (F : Forest)
    (h : checked T S q o=some F) :
    o=some F ∧ agreement T S F=true ∧ F.length-1≤q := by
  cases o with
  | none => simp [checked] at h
  | some G =>
    simp only [checked,Option.bind_some] at h
    split at h
    · rename_i hg
      have he : G=F := Option.some.inj h
      subst G
      simpa [accept] using hg
    · simp at h

theorem checked_complete (T S : Tree) (q : Nat) (F : Forest)
    (ha : agreement T S F=true) (hq : F.length-1≤q) :
    checked T S q (some F)=some F := by
  have hq' : F.length≤q+1 := by omega
  simp [checked,accept,ha,hq']

theorem choose_origin (a b : Option Forest) (F : Forest) (h : choose a b=some F) :
    a=some F ∨ b=some F := by
  cases a with
  | none => exact Or.inr (by simpa [choose] using h)
  | some G =>
    cases b with
    | none => exact Or.inl (by simpa [choose] using h)
    | some H =>
      simp only [choose] at h
      split at h
      · exact Or.inl h
      · exact Or.inr h

theorem choose_left_min (a b : Option Forest) (F : Forest) (ha : a=some F) :
    ∃ G, choose a b=some G ∧ G.length≤F.length := by
  subst a
  cases b with
  | none => exact ⟨F,rfl,Nat.le_refl _⟩
  | some H =>
    by_cases h : F.length≤H.length
    · exact ⟨F,by simp [choose,h],Nat.le_refl _⟩
    · exact ⟨H,by simp [choose,h],by omega⟩

theorem choose_right_min (a b : Option Forest) (F : Forest) (hb : b=some F) :
    ∃ G, choose a b=some G ∧ G.length≤F.length := by
  subst b
  cases a with
  | none => exact ⟨F,rfl,Nat.le_refl _⟩
  | some H =>
    by_cases h : H.length≤F.length
    · exact ⟨H,by simp [choose,h],h⟩
    · exact ⟨F,by simp [choose,h],Nat.le_refl _⟩

/-- Independent of any recursive oracle contract: the executable final check
    makes every returned forest an original agreement within global budget. -/
theorem execute_sound (solve : ForestSolver) (T S : Tree) (q : Nat)
    (xs : List Entry) (F : Forest) (h : (execute solve T S q xs).answer=some F) :
    agreement T S F=true ∧ F.length-1≤q := by
  induction xs with
  | nil => simp [execute] at h
  | cons e es ih =>
    change choose (checked T S q (dispatch solve T S e).answer)
      (execute solve T S q es).answer=some F at h
    rcases choose_origin _ _ F h with ha | hb
    · exact (checked_sound T S q _ F ha).2
    · exact ih hb

/-- The actual executable choice is no larger than every successfully checked
    candidate of every retained list occurrence, including duplicates. -/
theorem execute_complete (solve : ForestSolver) (T S : Tree) (q : Nat)
    (xs : List Entry) (e : Entry) (he : e∈xs) (F : Forest)
    (hf : (dispatch solve T S e).answer=some F)
    (ha : agreement T S F=true) (hq : F.length-1≤q) :
    ∃ G, (execute solve T S q xs).answer=some G ∧ G.length≤F.length := by
  induction xs with
  | nil => simp at he
  | cons a xs ih =>
    rcases List.mem_cons.1 he with he | he
    · subst a
      exact choose_left_min _ _ F (by rw [hf];exact checked_complete T S q F ha hq)
    · obtain ⟨H,hH,hmin⟩ := ih he
      obtain ⟨G,hG,hGH⟩ := choose_right_min (checked T S q (dispatch solve T S a).answer)
        (execute solve T S q xs).answer H hH
      exact ⟨G,hG,Nat.le_trans hGH hmin⟩

theorem execute_calls (solve : ForestSolver) (T S : Tree) (q : Nat) (xs : List Entry) :
    (execute solve T S q xs).calls=xs.flatMap (fun e => (dispatch solve T S e).calls) := by
  induction xs with
  | nil => rfl
  | cons e es ih => simp [execute,ih]

end Universal233.BothBad
