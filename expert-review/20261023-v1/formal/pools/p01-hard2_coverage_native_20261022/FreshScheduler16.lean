import FreshMeter14
open Universal233 PaidQueries
namespace FreshOrdinaryBridge
-- Fixed-budget structural proofs. The prior licensed bounded-forest structural
-- argument is source-guided reuse; all predicates here are exact fca originals.
theorem run_complete_fixed {P A : Type} (solve : P→Nat→Option (Nat×A))
    (b : Nat) (js : List (Job P A))
    (hc : ∀p,Job.hard p∈js → ∃x,solve p b=some x) :
    ∃xs,(run solve b js).answers=some xs := by
  induction js with
  | nil => exact ⟨[],rfl⟩
  | cons j js ih =>
    obtain ⟨ys,hy⟩:=ih (fun p hp=>hc p (by simp [hp]))
    cases j with
    | resolved p c a => exact ⟨(c,a)::ys,by simp [run,hy]⟩
    | hard p =>
      obtain ⟨x,hx⟩:=hc p (by simp)
      exact ⟨x::ys,by simp [run,hx,hy]⟩

theorem run_sound_fixed {P A : Type} (minimum : P→Nat) (valid : P→A→Prop)
    (solve : P→Nat→Option (Nat×A)) (b : Nat) (js : List (Job P A))
    (hp : ∀j∈js,Planned minimum valid j)
    (hs : ∀p,Job.hard p∈js → ∀c a,solve p b=some (c,a) → c=minimum p ∧ valid p a)
    (xs : List (Nat×A)) (hr : (run solve b js).answers=some xs) :
    AnswersFor minimum valid js xs := by
  induction js generalizing xs with
  | nil =>
    have he : xs=[] := by simpa [run] using hr.symm
    subst xs; exact .nil
  | cons j js ih =>
    have ht : ∀k∈js,Planned minimum valid k := fun k hk=>hp k (by simp [hk])
    have hst : ∀p,Job.hard p∈js → ∀c a,solve p b=some (c,a) → c=minimum p ∧ valid p a :=
      fun p h=>hs p (by simp [h])
    cases j with
    | resolved p c a =>
      cases he : (run solve b js).answers with
      | none => simp [run,he] at hr
      | some ys =>
        have hx : xs=(c,a)::ys := by simpa [run,he] using hr.symm
        subst xs
        have hh:=hp (.resolved p c a) (by simp)
        exact .cons ⟨hh.1,hh.2.1⟩ (ih ht hst ys he)
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
          exact .cons (hs p (by simp) c a he) (ih ht hst ys hrest)

theorem answers_cost_fixed {P A : Type} (minimum : P→Nat) (valid : P→A→Prop)
    (js : List (Job P A)) (xs : List (Nat×A))
    (ha : AnswersFor minimum valid js xs) :
    answerCost xs=totalMinimum minimum js ∧ xs.length=js.length := by
  induction ha with
  | nil => exact ⟨rfl,rfl⟩
  | @cons j x js xs hh ht ih =>
    simp only [answerCost,List.map_cons,List.sum_cons,totalMinimum,List.length_cons]
    exact ⟨by rw [hh.1]; exact congrArg (fun z=>minimum j.problem+z) ih.1,congrArg Nat.succ ih.2⟩

theorem planned_total_lower {P A : Type} (minimum : P→Nat) (valid : P→A→Prop)
    (js : List (Job P A)) (hp : ∀j∈js,Planned minimum valid j) :
    knownCost js+2*pending js≤totalMinimum minimum js := by
  induction js with
  | nil => simp only [knownCost,pending,totalMinimum]; omega
  | cons j js ih =>
    have ht:=ih (fun k hk=>hp k (by simp [hk]))
    have hh:=hp j (by simp)
    cases j with
    | resolved p c a =>
      change c=minimum p ∧ valid p a ∧ c≤1 at hh
      simp only [knownCost,pending,totalMinimum,Job.problem]
      omega
    | hard p =>
      change 2≤minimum p at hh
      simp only [knownCost,pending,totalMinimum,Job.problem]
      omega

theorem hard_pending_positive_fixed {P A : Type} (p : P) (js : List (Job P A))
    (hp : Job.hard p∈js) : 0<pending js := by
  induction js with
  | nil => exact False.elim (List.not_mem_nil hp)
  | cons j js ih =>
    cases j with
    | resolved r c a =>
      have ht : Job.hard p∈js := by simpa using hp
      exact ih ht
    | hard r => simp only [pending]; omega

theorem hard_other_lower_fixed {P A : Type} (minimum : P→Nat) (valid : P→A→Prop)
    (js : List (Job P A)) (hplan : ∀j∈js,Planned minimum valid j)
    (p : P) (hp : Job.hard p∈js) :
    minimum p+knownCost js+2*(pending js-1)≤totalMinimum minimum js := by
  induction js with
  | nil => exact False.elim (List.not_mem_nil hp)
  | cons j js ih =>
    have ht : ∀k∈js,Planned minimum valid k := fun k hk=>hplan k (by simp [hk])
    have hh:=hplan j (by simp)
    rcases List.mem_cons.mp hp with he|hp
    · subst j
      have lower:=planned_total_lower minimum valid js ht
      simp only [knownCost,pending,totalMinimum,Job.problem]
      omega
    · have other:=ih ht hp
      have pos:=hard_pending_positive_fixed p js hp
      cases j with
      | resolved r c a =>
        change c=minimum r ∧ valid r a ∧ c≤1 at hh
        simp only [knownCost,pending,totalMinimum,Job.problem]
        omega
      | hard r =>
        change 2≤minimum r at hh
        simp only [knownCost,pending,totalMinimum,Job.problem]
        omega

theorem allocation_feasible_fixed {P A : Type} (minimum : P→Nat) (valid : P→A→Prop)
    (q : Nat) (js : List (Job P A)) (hplan : ∀j∈js,Planned minimum valid j)
    (hq : totalMinimum minimum js≤q) (p : P) (hp : Job.hard p∈js) :
    minimum p≤allocated q js := by
  have lower:=hard_other_lower_fixed minimum valid js hplan p hp
  unfold allocated
  omega

theorem schedule_complete_fixed {P A : Type} (minimum : P→Nat) (valid : P→A→Prop)
    (solve : P→Nat→Option (Nat×A)) (q : Nat) (js : List (Job P A))
    (hplan : ∀j∈js,Planned minimum valid j)
    (hs : ∀p,Job.hard p∈js → ∀c a,solve p (allocated q js)=some (c,a) → c=minimum p ∧ valid p a)
    (hc : ∀p,Job.hard p∈js → minimum p≤allocated q js → ∃x,solve p (allocated q js)=some x)
    (hq : totalMinimum minimum js≤q) :
    ∃xs,(schedule solve q js).answers=some xs ∧ AnswersFor minimum valid js xs ∧
      answerCost xs=totalMinimum minimum js := by
  have hguard : ¬q<knownCost js+2*pending js := by
    have := planned_total_lower minimum valid js hplan
    omega
  obtain ⟨xs,hxs⟩:=run_complete_fixed solve (allocated q js) js
    (fun p hp=>hc p hp (allocation_feasible_fixed minimum valid q js hplan hq p hp))
  have ha:=run_sound_fixed minimum valid solve (allocated q js) js hplan hs xs hxs
  have cost:=(answers_cost_fixed minimum valid js xs ha).1
  refine ⟨xs,?_,ha,cost⟩
  simp only [schedule,if_neg hguard,hxs,Option.bind_some]
  rw [if_pos (show answerCost xs≤q by omega)]

theorem schedule_sound_fixed {P A : Type} (minimum : P→Nat) (valid : P→A→Prop)
    (solve : P→Nat→Option (Nat×A)) (q : Nat) (js : List (Job P A))
    (hplan : ∀j∈js,Planned minimum valid j)
    (hs : ∀p,Job.hard p∈js → ∀c a,solve p (allocated q js)=some (c,a) → c=minimum p ∧ valid p a)
    (xs : List (Nat×A)) (hr : (schedule solve q js).answers=some xs) :
    AnswersFor minimum valid js xs ∧ answerCost xs=totalMinimum minimum js ∧
      totalMinimum minimum js≤q := by
  by_cases guard : q<knownCost js+2*pending js
  · simp only [schedule,if_pos guard] at hr
    cases hr
  · simp only [schedule,if_neg guard] at hr
    cases hrun : (run solve (allocated q js) js).answers with
    | none => simp only [hrun,Option.bind_none] at hr; cases hr
    | some ys =>
      simp only [hrun,Option.bind_some] at hr
      by_cases cost : answerCost ys≤q
      · rw [if_pos cost] at hr
        have he : ys=xs := Option.some.inj hr
        subst ys
        have ha:=run_sound_fixed minimum valid solve (allocated q js) js hplan hs xs hrun
        have hc:=(answers_cost_fixed minimum valid js xs ha).1
        exact ⟨ha,hc,by omega⟩
      · rw [if_neg cost] at hr
        cases hr
end FreshOrdinaryBridge

-- Author integration type/axiom reports; proof text above is unchanged apart from recorded import edits.
set_option pp.universes true
#check @FreshOrdinaryBridge.run_complete_fixed
#print axioms FreshOrdinaryBridge.run_complete_fixed
#check @FreshOrdinaryBridge.run_sound_fixed
#print axioms FreshOrdinaryBridge.run_sound_fixed
#check @FreshOrdinaryBridge.answers_cost_fixed
#print axioms FreshOrdinaryBridge.answers_cost_fixed
#check @FreshOrdinaryBridge.planned_total_lower
#print axioms FreshOrdinaryBridge.planned_total_lower
#check @FreshOrdinaryBridge.hard_pending_positive_fixed
#print axioms FreshOrdinaryBridge.hard_pending_positive_fixed
#check @FreshOrdinaryBridge.hard_other_lower_fixed
#print axioms FreshOrdinaryBridge.hard_other_lower_fixed
#check @FreshOrdinaryBridge.allocation_feasible_fixed
#print axioms FreshOrdinaryBridge.allocation_feasible_fixed
#check @FreshOrdinaryBridge.schedule_complete_fixed
#print axioms FreshOrdinaryBridge.schedule_complete_fixed
#check @FreshOrdinaryBridge.schedule_sound_fixed
#print axioms FreshOrdinaryBridge.schedule_sound_fixed
