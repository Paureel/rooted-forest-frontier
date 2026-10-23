import ActualBadSlots
namespace Universal233.BothBad
open RMAF CoreProgram PaidQueries SourceCoverage

theorem traceMass_shift (c : Rat) (hc : 2≤c) (q b d : Nat) (xs : List Call)
    (hq : b+d=q) (caps : ∀ a∈xs, a.budget≤b) :
    traceMass c q xs=c^(-(d : Int))*traceMass c b xs := by
  have cn : c≠0 := Rat.ne_of_gt (by grind : 0<c)
  induction xs with
  | nil => simp [traceMass,actualQueryMass]
  | cons a xs ih =>
    have cap := caps a (by simp)
    have ht := ih (fun x hx => caps x (by simp [hx]))
    have exp : -((q-a.budget : Nat) : Int)=-(d : Int)+-((b-a.budget : Nat) : Int) := by omega
    simp only [traceMass,actualQueryMass,List.map_cons,List.sum_cons] at ht ⊢
    rw [exp,Rat.zpow_add cn,ht,Rat.mul_add]

theorem full_dispatch_mass (solve : ForestSolver) (T S : Tree) (o : Output) (q b : Nat)
    (hq : b+o.sourceCuts.length=q) (c : Rat) :
    traceMass c q (dispatch solve T S ⟨o,.full,b⟩).calls=c^(-(o.sourceCuts.length : Int)) := by
  have h : q-b=o.sourceCuts.length := by omega
  simp [dispatch,traceMass,actualQueryMass,h,Rat.add_zero]

theorem retained_dispatch_mass (solve : ForestSolver) (T S : Tree) (o : Output)
    (A B C : List Nat) (F : Forest) (q b : Nat)
    (hq : b+o.sourceCuts.length+1=q) (c : Rat) (hc : 2≤c) :
    traceMass c q (dispatch solve T S ⟨o,.retained A B C F,b⟩).calls=
      c^(-(o.sourceCuts.length : Int))*c^(-1 : Int) := by
  have h : -((q-b : Nat) : Int)=-(o.sourceCuts.length : Int)+(-1) := by omega
  simp only [dispatch,traceMass,actualQueryMass,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,Rat.add_zero]
  rw [h,Rat.zpow_add (Rat.ne_of_gt (by grind : 0<c))]

theorem ordinary_dispatch_mass (solve : ForestSolver) (T S : Tree) (o : Output) (q b : Nat)
    (hq : b+o.sourceCuts.length=q) (c : Rat) (hc : 2≤c) :
    traceMass c q (dispatch solve T S ⟨o,.ordinary,b⟩).calls≤c^(-(o.sourceCuts.length : Int)) := by
  change traceMass c q (ordinaryExecution solve T S o.partition b).calls≤_
  rw [traceMass_shift c hc q b o.sourceCuts.length _ hq (ordinary_budget_cap solve T S o.partition b)]
  have h := Rat.mul_le_mul_of_nonneg_left (ordinary_mass_one solve T S o.partition b c hc)
    (Rat.le_of_lt (Rat.zpow_pos (a:=c) (n:= -(o.sourceCuts.length : Int)) (by grind : 0<c)))
  simpa only [Rat.mul_one] using h

theorem ordinary_dispatch_paid_mass (solve : ForestSolver) (T S : Tree) (o : Output) (q b : Nat)
    (hq : b+o.sourceCuts.length=q) (c : Rat) (hc : 2≤c) (hb : BinaryCheap.TwoBad S T o) :
    traceMass c q (dispatch solve T S ⟨o,.ordinary,b⟩).calls≤
      c^(-(o.sourceCuts.length : Int))*c^(-1 : Int) := by
  change traceMass c q (ordinaryExecution solve T S o.partition b).calls≤_
  rw [traceMass_shift c hc q b o.sourceCuts.length _ hq (ordinary_budget_cap solve T S o.partition b)]
  exact Rat.mul_le_mul_of_nonneg_left (ordinary_mass_paid solve T S o b c hc hb)
    (Rat.le_of_lt (Rat.zpow_pos (by grind : 0<c)))

def entryMass (solve : ForestSolver) (T S : Tree) (c : Rat) (q : Nat) (xs : List Entry) : Rat :=
  (xs.map (fun e => traceMass c q (dispatch solve T S e).calls)).sum

theorem execute_mass (solve : ForestSolver) (T S : Tree) (c : Rat) (q : Nat) (xs : List Entry) :
    traceMass c q (execute solve T S q xs).calls=entryMass solve T S c q xs := by
  induction xs with
  | nil => rfl
  | cons e xs ih =>
    change traceMass c q ((dispatch solve T S e).calls++(execute solve T S q xs).calls)=_
    rw [traceMass_append,ih]
    rfl

theorem entryMass_append (solve : ForestSolver) (T S : Tree) (c : Rat) (q : Nat) (xs ys : List Entry) :
    entryMass solve T S c q (xs++ys)=entryMass solve T S c q xs+entryMass solve T S c q ys := by
  simp [entryMass,List.map_append,List.sum_append]

/-- Filtered-out occurrences contribute zero callbacks; all retained duplicate
occurrences are counted separately. No value-list counting replaces a trace. -/
theorem entries_mass_bound (solve : ForestSolver) (T S : Tree) (c : Rat) (hc : 2≤c)
    (q : Nat) (mode : Mode) (xs : List Output) (factor : Rat) (hf : 0≤factor)
    (bound : ∀ o∈xs, o.sourceCuts.length+mode.extra≤q →
      traceMass c q (dispatch solve T S ⟨o,mode,q-o.sourceCuts.length-mode.extra⟩).calls≤
        c^(-(o.sourceCuts.length : Int))*factor) :
    entryMass solve T S c q (entries q mode xs)≤rawQMass c xs*factor := by
  induction xs with
  | nil => simp [entries,entryMass,rawQMass]
  | cons o xs ih =>
    have ht := ih (fun z hz => bound z (by simp [hz]))
    by_cases hb : o.sourceCuts.length+mode.extra≤q
    · have hcur := bound o (by simp) hb
      simp only [entries,List.filterMap_cons,hb,ite_true,entryMass,List.map_cons,List.sum_cons,rawQMass] at ht ⊢
      rw [Rat.add_mul]
      exact SourceCoverage.qadd_le_add hcur ht
    · have nonneg := Rat.mul_nonneg (Rat.le_of_lt (Rat.zpow_pos (a:=c)
        (n:= -(o.sourceCuts.length : Int)) (by grind : 0<c))) hf
      simp only [entries,List.filterMap_cons,hb,ite_false,entryMass,List.map_cons,List.sum_cons,rawQMass] at ht ⊢
      rw [Rat.add_mul]
      grind

theorem full_entries_mass (solve : ForestSolver) (T S : Tree) (c : Rat) (hc : 2≤c)
    (q : Nat) (xs : List Output) :
    entryMass solve T S c q (entries q .full xs)≤rawQMass c xs := by
  have h := entries_mass_bound solve T S c hc q .full xs 1 (by decide) (by
    intro o ho hb
    have hq : q-o.sourceCuts.length+o.sourceCuts.length=q := by simp only [Mode.extra] at hb;omega
    simp only [Mode.extra,Nat.sub_zero,Rat.mul_one]
    rw [full_dispatch_mass solve T S o q _ hq c]
    exact Rat.le_refl)
  simpa only [Rat.mul_one] using h
end Universal233.BothBad
