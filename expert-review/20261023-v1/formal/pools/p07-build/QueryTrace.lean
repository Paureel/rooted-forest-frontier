import PlanCover
namespace Universal233.BothBad
open RMAF CoreProgram PaidQueries MafScheduler

def traceMass (c : Rat) (q : Nat) (calls : List Call) : Rat :=
  actualQueryMass c q (calls.map Call.budget)

theorem traceMass_nonneg (c : Rat) (hc : 2≤c) (q : Nat) (calls : List Call) :
    0≤traceMass c q calls := by
  induction calls with
  | nil => simp [traceMass,actualQueryMass]
  | cons a calls ih =>
    exact Rat.add_nonneg (Rat.le_of_lt (Rat.zpow_pos (by grind : 0<c))) ih

theorem traceMass_append (c : Rat) (q : Nat) (xs ys : List Call) :
    traceMass c q (xs++ys)=traceMass c q xs+traceMass c q ys := by
  simp [traceMass,actualQueryMass,List.map_append,List.sum_append]

theorem meterSchedule_budgets (f : P → Nat → Option (Nat × A)) (charge : P → Nat → Nat)
    (q : Nat) (js : List (Job P A)) :
    ((meterSchedule f charge q js).queries.map Prod.snd)=(schedule f q js).calls := by
  unfold meterSchedule schedule
  split
  · rfl
  · exact (meterRun_trace f charge _ js).1

theorem queryEnvelope_le_one (c : Rat) (hc : 2≤c) (js : List (Job P A)) :
    queryEnvelope c js≤1 := by
  cases hp : pending js with
  | zero => simpa [queryEnvelope,hp] using (show (0 : Rat)≤1 by decide)
  | succ p =>
    cases p with
    | zero =>
      have h := negpow_antitone c hc 0 (knownCost js) (by omega)
      simpa [queryEnvelope,hp] using h
    | succ p =>
      have hmulti := multi_hard_mass c hc (pending js) (by omega)
      have hmono := negpow_antitone c hc (2*(pending js-1))
        (knownCost js+2*(pending js-1)) (by omega)
      have hmul := Rat.mul_le_mul_of_nonneg_left hmono (show 0≤(pending js : Rat) from Rat.natCast_nonneg)
      have h1 := negpow_antitone c hc 0 1 (by omega)
      exact Rat.le_trans (Rat.le_trans hmul hmulti) (by simpa using h1)

def liftQueries (T S : Tree) (xs : List (List Nat × Nat)) : List Call :=
  xs.filterMap (fun ub => match restrict ub.1 T,restrict ub.1 S with
    | some t,some s => some ⟨some t,[s],ub.2⟩
    | _,_ => none)

theorem lift_mass_le (T S : Tree) (c : Rat) (hc : 2≤c) (q : Nat)
    (xs : List (List Nat × Nat)) :
    traceMass c q (liftQueries T S xs)≤actualQueryMass c q (xs.map Prod.snd) := by
  induction xs with
  | nil => simp [liftQueries,traceMass,actualQueryMass]
  | cons ub xs ih =>
    rcases ub with ⟨U,b⟩
    have nonneg := Rat.le_of_lt (Rat.zpow_pos (a:=c) (n:= -((q-b : Nat) : Int)) (by grind : 0<c))
    cases ht : restrict U T <;> cases hs : restrict U S <;>
      simp [liftQueries,ht,hs,traceMass,actualQueryMass] at ih ⊢ <;> grind

theorem ordinary_mass_le_calls (solve : ForestSolver) (T S : Tree) (Q : Forest)
    (b : Nat) (c : Rat) (hc : 2≤c) :
    traceMass c b (ordinaryExecution solve T S Q b).calls≤
      actualQueryMass c b (MafScheduler.calls T S (asTree solve) b Q) := by
  cases hp : prepare T S Q with
  | none => simp [ordinaryExecution,MafScheduler.calls,MafScheduler.attempt,hp,traceMass,actualQueryMass]
  | some js =>
    have h := lift_mass_le T S c hc b (meterSchedule (recursive T S (asTree solve)) (fun _ _ => 0) b js).queries
    rw [meterSchedule_budgets] at h
    have hcalls : MafScheduler.calls T S (asTree solve) b Q=(schedule (recursive T S (asTree solve)) b js).calls := by
      simp [MafScheduler.calls,MafScheduler.attempt,hp]
    rw [hcalls]
    simp only [ordinaryExecution,hp]
    exact h

theorem ordinary_mass_one (solve : ForestSolver) (T S : Tree) (Q : Forest)
    (b : Nat) (c : Rat) (hc : 2≤c) :
    traceMass c b (ordinaryExecution solve T S Q b).calls≤1 := by
  apply Rat.le_trans (ordinary_mass_le_calls solve T S Q b c hc)
  cases hp : prepare T S Q with
  | none => simp only [MafScheduler.calls,MafScheduler.attempt,hp,Option.map_none,Option.getD_none,actualQueryMass,List.map_nil,List.sum_nil];decide
  | some js =>
    have h := actual_query_envelope (recursive T S (asTree solve)) b js c hc
    have h1 := queryEnvelope_le_one c hc js
    simpa [MafScheduler.calls,MafScheduler.attempt,hp] using Rat.le_trans h h1

theorem ordinary_budget_cap (solve : ForestSolver) (T S : Tree) (Q : Forest) (b : Nat) :
    ∀ a∈(ordinaryExecution solve T S Q b).calls, a.budget≤b := by
  intro a ha
  cases hp : prepare T S Q with
  | none => simp [ordinaryExecution,hp] at ha
  | some js =>
    simp only [ordinaryExecution,hp] at ha
    change a∈liftQueries T S (meterSchedule (recursive T S (asTree solve)) (fun _ _ => 0) b js).queries at ha
    obtain ⟨ub,hub,hmap⟩ := List.mem_filterMap.1 ha
    have hquery : ub.2∈(schedule (recursive T S (asTree solve)) b js).calls := by
      rw [←meterSchedule_budgets (recursive T S (asTree solve)) (fun _ _ => 0)]
      exact List.mem_map.2 ⟨ub,hub,rfl⟩
    have cap : ub.2≤b := by
      have ht := schedule_trace (recursive T S (asTree solve)) b js
      have he := ht.2.1 ub.2 hquery
      rw [he]
      unfold allocated
      omega
    cases hT : restrict ub.1 T <;> cases hS : restrict ub.1 S <;> simp only [hT,hS] at hmap
    all_goals first | contradiction | (have he := Option.some.inj hmap;subst a;exact cap)

end Universal233.BothBad
