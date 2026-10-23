import QueryTrace
namespace Universal233.BothBad
open RMAF PaidQueries MafScheduler

def jobBad : Job P A → Nat
  | .resolved _ c _ => if c=0 then 0 else 1
  | .hard _ => 1

theorem badSlots_cons (j : Job P A) (js : List (Job P A)) :
    badSlots (j::js)=jobBad j+badSlots js := by cases j <;> rfl

/-- The executable pretest itself supplies the bad-slot charge. No optimum
oracle or solution existence is needed to bound a failing query trace. -/
theorem slot_bad (T S : Tree) (U : List Nat) (j : Job (List Nat) Forest)
    (hj : slot T S U=some j) : (if restrictionAgrees T S U then 0 else 1)≤jobBad j := by
  unfold slot at hj
  split at hj
  · simp at hj
  · cases ht : restrict U T with
    | none => simp [ht] at hj
    | some t =>
      cases hs : restrict U S with
      | none => simp [ht,hs] at hj
      | some s =>
        cases hp : DepthOne.pretest01 t s with
        | refused => simp [ht,hs,hp] at hj
        | rejected =>
          have he : j=.hard U := (Option.some.inj (by simpa [ht,hs,hp] using hj)).symm
          subst j
          simp only [jobBad]
          split <;> omega
        | found c =>
          have he : j=.resolved U (DepthOne.cutCost c) (DepthOne.forest s c) :=
            (Option.some.inj (by simpa [ht,hs,hp] using hj)).symm
          subst j
          cases c with
          | some p => simp [jobBad,DepthOne.cutCost];split <;> omega
          | none =>
            have ha := (DepthOne.found_globally_minimum t s none hp).1
            have shape := agreement_single_sameShape t s (leaves s) ha
            simp [jobBad,DepthOne.cutCost,restrictionAgrees,ht,hs,shape]

theorem prepare_bad (T S : Tree) (Q : Forest) (js : List (Job (List Nat) Forest))
    (hp : prepare T S Q=some js) : badParents T S Q≤badSlots js := by
  induction Q generalizing js with
  | nil => have he : js=[] := (Option.some.inj hp).symm;subst js;simp [badParents,badSlots]
  | cons U Q ih =>
    cases hj : slot T S U with
    | none => simp [prepare,hj] at hp
    | some j =>
      cases hr : prepare T S Q with
      | none => simp [prepare,hj,hr] at hp
      | some rs =>
        have he : js=j::rs := (Option.some.inj (by simpa [prepare,hj,hr] using hp)).symm
        subst js
        have hh := slot_bad T S U j hj
        have ht := ih rs hr
        simp only [badParents,List.map_cons,List.sum_cons] at ht ⊢
        rw [badSlots_cons]
        omega

theorem positive_sum_one {α : Type} (f : α → Nat) (xs : List α) (x : α)
    (hx : x∈xs) (hf : 1≤f x) : 1≤(xs.map f).sum := by
  induction xs with
  | nil => simp at hx
  | cons a xs ih =>
    rcases List.mem_cons.1 hx with he | he
    · subst a;simp only [List.map_cons,List.sum_cons];omega
    · have := ih he;simp only [List.map_cons,List.sum_cons];omega

theorem positive_sum_two {α : Type} (f : α → Nat) (xs : List α) (x y : α)
    (hx : x∈xs) (hy : y∈xs) (hne : x≠y) (fx : 1≤f x) (fy : 1≤f y) : 2≤(xs.map f).sum := by
  induction xs with
  | nil => simp at hx
  | cons a xs ih =>
    rcases List.mem_cons.1 hx with he | he
    · subst a
      have hy' : y∈xs := by rcases List.mem_cons.1 hy with h | h;exact False.elim (hne h.symm);exact h
      have := positive_sum_one f xs y hy' fy
      simp only [List.map_cons,List.sum_cons];omega
    · rcases List.mem_cons.1 hy with hy | hy
      · subst a
        have := positive_sum_one f xs x he fx
        simp only [List.map_cons,List.sum_cons];omega
      · have := ih he hy
        simp only [List.map_cons,List.sum_cons];omega

theorem twoBad_count (T S : Tree) (o : CoreProgram.Output) (hb : BinaryCheap.TwoBad S T o) :
    2≤badParents T S o.partition := by
  obtain ⟨K,L,hK,hL,hne,hbadK,hbadL,hdisj⟩ := hb
  have hK' : restrictionAgrees T S K=false := by
    cases h : restrictionAgrees T S K with
    | false => rfl
    | true => have hh := PairAssembly.restriction_agrees_swap T S K h;simp [hbadK] at hh
  have hL' : restrictionAgrees T S L=false := by
    cases h : restrictionAgrees T S L with
    | false => rfl
    | true => have hh := PairAssembly.restriction_agrees_swap T S L h;simp [hbadL] at hh
  exact positive_sum_two (fun U => if restrictionAgrees T S U then 0 else 1) o.partition K L hK hL hne
    (by simp [hK']) (by simp [hL'])

theorem ordinary_mass_paid (solve : ForestSolver) (T S : Tree) (o : CoreProgram.Output)
    (b : Nat) (c : Rat) (hc : 2≤c) (hbad : BinaryCheap.TwoBad S T o) :
    traceMass c b (ordinaryExecution solve T S o.partition b).calls≤c^(-1 : Int) := by
  apply Rat.le_trans (ordinary_mass_le_calls solve T S o.partition b c hc)
  cases hp : prepare T S o.partition with
  | none =>
    simp only [MafScheduler.calls,MafScheduler.attempt,hp,Option.map_none,Option.getD_none,actualQueryMass,List.map_nil,List.sum_nil]
    exact Rat.le_of_lt (Rat.zpow_pos (by grind : 0<c))
  | some js =>
    have hcount := prepare_bad T S o.partition js hp
    have hb := twoBad_count T S o hbad
    have h := actual_paid_query_mass (recursive T S (asTree solve)) b js (by omega) c hc
    simpa [MafScheduler.calls,MafScheduler.attempt,hp] using h
end Universal233.BothBad
