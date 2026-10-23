import FullStateJobs
namespace Universal233.GroupedFullQuery
open RMAF ForestState ForestGroups PaidQueries ForestMinCompletion

def BelowIH (q : Nat) (actual : Ordinary) : Prop := ∀ r,r<q → LocalOrdinaryIH r actual
/-- Literal full-current-state solver call, with the original actual callback. -/
def callback (actual : Ordinary) (p : Problem) (b : Nat) : Option (Nat × Forest) :=
 (GenericForest.solve actual p.target p.sources b).map (fun F => (cost p F,F))

theorem callback_spec (actual : Ordinary) (q : Nat) (below : BelowIH q actual)
 (p : Problem) (b : Nat) (hb : b<q) (c : Nat) (F : Forest)
 (h : callback actual p b=some (c,F)) : valid p F ∧ c=cost p F ∧ least p F := by
 cases he : GenericForest.solve actual p.target p.sources b with
 | none => simp [callback,he] at h
 | some G =>
   have eq : (cost p G,G)=(c,F) := by simpa [callback,he] using h
   cases eq
   have hs := GenericForest.solve_sound actual p.target p.sources b F he
   refine ⟨hs.1,rfl,?_⟩
   intro H hH
   exact Nat.sub_le_sub_right
    (Rule5PaidOrdinary.actual_solve_minimum actual p.target p.sources b (below b hb) he H hH) _

theorem callback_complete (actual : Ordinary) (q : Nat) (below : BelowIH q actual)
 (p : Problem) (b : Nat) (hb : b<q) (G : Forest) (hG : valid p G) (budget : cost p G≤b) :
 ∃ x,callback actual p b=some x := by
 obtain ⟨F,hF,_⟩ := GenericForest.LocalIH.exact_at_current_budget actual b (below b hb)
   p.target p.sources G hG budget
 exact ⟨(cost p F,F),by simp [callback,hF]⟩

inductive Answers : List (Job Problem Forest) → List (Nat × Forest) → Prop
 | nil : Answers [] []
 | cons {j : Job Problem Forest} {x : Nat × Forest} {js} {xs} :
   (valid j.problem x.2 ∧ x.1=cost j.problem x.2 ∧ least j.problem x.2) →
   Answers js xs → Answers (j::js) (x::xs)

def potential (H : Problem → Forest) : List (Job Problem Forest) → Nat
 | [] => 0
 | j::js => cost j.problem (H j.problem)+potential H js

def Supports (H : Problem → Forest) (js : List (Job Problem Forest)) : Prop :=
 ∀ j∈js,valid j.problem (H j.problem)

theorem answers_le (H : Problem → Forest) {js} {xs} (a : Answers js xs) (hH : Supports H js) :
 answerCost xs≤potential H js := by
 induction a with
 | nil => simp [answerCost,potential]
 | @cons j x js xs hx ha ih =>
   have hh := hx.2.2 (H j.problem) (hH j (by simp))
   have ht := ih (fun k hk => hH k (by simp [hk]))
   simp only [answerCost,List.map_cons,List.sum_cons,potential] at *
   omega

theorem lower_bound (H : Problem → Forest) (js : List (Job Problem Forest))
 (plan : ∀ j∈js,Planned j) (hH : Supports H js) :
 knownCost js+2*pending js≤potential H js := by
 induction js with
 | nil => simp [knownCost,pending,potential]
 | cons j js ih =>
   have tail := ih (fun k hk => plan k (by simp [hk])) (fun k hk => hH k (by simp [hk]))
   have hj := plan j (by simp)
   have hh := hH j (by simp)
   cases j with
   | resolved p c F =>
     have low := hj.2.2.1 (H p) hh
     simp only [Job.problem,knownCost,pending,potential]
     simp only [Planned] at hj
     omega
   | hard p =>
     have low := hj.2 (H p) hh
     simp only [Job.problem,knownCost,pending,potential]
     omega

theorem other_lower (H : Problem → Forest) (js : List (Job Problem Forest))
 (plan : ∀ j∈js,Planned j) (hH : Supports H js) (p : Problem) (hp : Job.hard p∈js) :
 cost p (H p)+knownCost js+2*(pending js-1)≤potential H js := by
 induction js with
 | nil => simp at hp
 | cons j js ih =>
   have pt : ∀ k∈js,Planned k := fun k hk => plan k (by simp [hk])
   have st : Supports H js := fun k hk => hH k (by simp [hk])
   have hj := plan j (by simp)
   have hh := hH j (by simp)
   cases j with
   | resolved u c F =>
     have hm : Job.hard p∈js := by simpa using hp
     have hi := ih pt st hm
     have low := hj.2.2.1 (H u) hh
     simp only [Planned] at hj
     simp only [Job.problem,knownCost,pending,potential]
     omega
   | hard u =>
     rcases List.mem_cons.1 hp with he|hm
     · have eq : p=u := by cases he;rfl
       subst u
       have hl := lower_bound H js pt st
       simp only [Job.problem,knownCost,pending,potential]
       omega
     · have hi := ih pt st hm
       have hn := hard_pending_positive p js hm
       have low := hj.2 (H u) hh
       simp only [Job.problem,knownCost,pending,potential]
       omega

theorem run_sound_at (actual : Ordinary) (q : Nat) (below : BelowIH q actual)
 (b : Nat) (js : List (Job Problem Forest))
 (low : 0<pending js → b<q) (plan : ∀ j∈js,Planned j)
 (xs : List (Nat × Forest)) (h : (run (callback actual) b js).answers=some xs) : Answers js xs := by
 induction js generalizing xs with
 | nil =>
   have eq : xs=[] := by simpa [run] using h.symm
   subst xs;exact Answers.nil
 | cons j js ih =>
   have pt : ∀ k∈js,Planned k := fun k hk => plan k (by simp [hk])
   cases j with
   | resolved p c F =>
     cases ht : (run (callback actual) b js).answers with
     | none => simp [run,ht] at h
     | some ys =>
       have eq : xs=(c,F)::ys := by simpa [run,ht] using h.symm
       subst xs
       have hj := plan (.resolved p c F) (by simp)
       exact Answers.cons ⟨hj.1,hj.2.1,hj.2.2.1⟩ (ih low pt ys ht)
   | hard p =>
     have hb : b<q := low (by simp [pending])
     cases hc : callback actual p b with
     | none => simp [run,hc] at h
     | some x =>
       cases ht : (run (callback actual) b js).answers with
       | none => simp [run,hc,ht] at h
       | some ys =>
         have eq : xs=x::ys := by simpa [run,hc,ht] using h.symm
         subst xs
         exact Answers.cons (callback_spec actual q below p b hb x.1 x.2 hc)
           (ih (fun _ => hb) pt ys ht)

theorem run_complete_at (actual : Ordinary) (q : Nat) (below : BelowIH q actual)
 (b : Nat) (js : List (Job Problem Forest)) (H : Problem → Forest)
 (low : 0<pending js → b<q) (hH : Supports H js)
 (fits : ∀ p,Job.hard p∈js → cost p (H p)≤b) :
 ∃ xs,(run (callback actual) b js).answers=some xs := by
 induction js with
 | nil => exact ⟨[],rfl⟩
 | cons j js ih =>
   have st : Supports H js := fun k hk => hH k (by simp [hk])
   have ft : ∀ p,Job.hard p∈js → cost p (H p)≤b := fun p hp => fits p (by simp [hp])
   cases j with
   | resolved p c F =>
     obtain ⟨ys,hy⟩ := ih low st ft
     exact ⟨(c,F)::ys,by simp [run,hy]⟩
   | hard p =>
     have hb := low (by simp [pending])
     obtain ⟨ys,hy⟩ := ih (fun _ => hb) st ft
     obtain ⟨x,hx⟩ := callback_complete actual q below p b hb (H p)
       (hH (.hard p) (by simp)) (fits p (by simp))
     exact ⟨x::ys,by simp [run,hx,hy]⟩

theorem allocated_strict (q : Nat) (js : List (Job Problem Forest))
 (bad : 2≤badSlots js) (active : knownCost js+2*pending js≤q) :
 0<pending js → allocated q js<q := by
 have hb := bad_le_known_pending js
 simp only [allocated]
 omega

theorem schedule_sound_at (actual : Ordinary) (q : Nat) (below : BelowIH q actual)
 (js : List (Job Problem Forest)) (bad : 2≤badSlots js) (plan : ∀ j∈js,Planned j)
 (xs : List (Nat × Forest)) (h : (schedule (callback actual) q js).answers=some xs) :
 Answers js xs ∧ answerCost xs≤q := by
 unfold schedule at h
 split at h
 · simp at h
 · rename_i active
   cases hr : (run (callback actual) (allocated q js) js).answers with
   | none => simp [hr] at h
   | some ys =>
     by_cases budget : answerCost ys≤q
     · have eq : xs=ys := by simpa [hr,budget] using h.symm
       subst xs
       exact ⟨run_sound_at actual q below _ js (allocated_strict q js bad (by omega)) plan ys hr,budget⟩
     · simp [hr,budget] at h

theorem schedule_complete_at (actual : Ordinary) (q : Nat) (below : BelowIH q actual)
 (js : List (Job Problem Forest)) (bad : 2≤badSlots js) (plan : ∀ j∈js,Planned j)
 (H : Problem → Forest) (hH : Supports H js) (budget : potential H js≤q) :
 ∃ xs,(schedule (callback actual) q js).answers=some xs ∧ Answers js xs ∧ answerCost xs≤potential H js := by
 have lb := lower_bound H js plan hH
 have active : knownCost js+2*pending js≤q := by omega
 have low := allocated_strict q js bad active
 have fits : ∀ p,Job.hard p∈js → cost p (H p)≤allocated q js := by
   intro p hp
   have hl := other_lower H js plan hH p hp
   simp only [allocated]
   omega
 obtain ⟨xs,hr⟩ := run_complete_at actual q below _ js H low hH fits
 have sound := run_sound_at actual q below _ js low plan xs hr
 have best := answers_le H sound hH
 refine ⟨xs,?_,sound,best⟩
 simp [schedule,show ¬q<knownCost js+2*pending js by omega,hr,show answerCost xs≤q by omega]

theorem actual_mass (actual : Ordinary) (q : Nat) (js : List (Job Problem Forest))
 (bad : 2≤badSlots js) (c : Rat) (hc : 2≤c) :
 actualQueryMass c q (schedule (callback actual) q js).calls≤c^(-1 : Int) :=
 actual_paid_query_mass (callback actual) q js bad c hc

theorem actual_query_strict (actual : Ordinary) (q : Nat) (js : List (Job Problem Forest))
 (bad : 2≤badSlots js) (r : Nat) (hr : r∈(schedule (callback actual) q js).calls) : r<q := by
 have h := every_query_loses_unit (callback actual) q js bad r hr
 omega
end Universal233.GroupedFullQuery
