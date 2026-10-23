-- Rebased source replay in completed selected-one slim environment; zero new independent/reconstruction credit.
-- Reconstructed local paid-job support after executed controls.
-- Source-guided continuation: no independent/blind/reconstruction credit.
-- The refused jobs_planned/found_globally_minimum chain is never applied.
import LocalExact
open RMAF ForestState GenericForest
open Universal233 Universal233.PaidQueries Universal233.MafScheduler
namespace PaidInstanceForest

theorem found_minimum_direct (T S : Tree) (c : Option RMAF.Vertex)
 (h : DepthOne.pretest01 T S=.found c) :
 agreement T S (DepthOne.forest S c)=true ∧
 (DepthOne.forest S c).length-1=DepthOne.cutCost c ∧
 ∀F,agreement T S F=true → DepthOne.cutCost c≤F.length-1 := by
 obtain ⟨hp,hc,ha,least⟩:=DepthOne.found_spec T S c h
 refine ⟨ha,by cases c <;> simp [DepthOne.forest,DepthOne.cutCost],?_⟩
 intro F hF
 by_cases small : F.length-1≤1
 · obtain ⟨d,hd,hda,hbound⟩:=DepthOne.candidate_complete T S F
     ((DepthOne.proper_iff T S).mp hp).2.1 hF small
   exact Nat.le_trans (least d hd hda) hbound
 · have hc:=DepthOne.cutCost_le_one c
   omega

theorem jobs_planned_direct (t : Tree) (ss : List Tree) (m : Tree×Tree→Nat)
 (actual : ∀s∈ss,componentPair t s=some (pair t s))
 (pp : ∀s∈ss,DepthOne.proper (pair t s).1 (pair t s).2=true)
 (mm : ∀s∈ss,LocalMinimum (pair t s).1 (pair t s).2 (m (pair t s))) :
 ∃js,jobs t ss=some js ∧ js.map Job.problem=ss.map (pair t) ∧
 ∀j∈js,Planned m (PairValid m) j := by
 induction ss with
 | nil => exact ⟨[],rfl,rfl,by simp⟩
 | cons s ss ih =>
   obtain ⟨tail,ht,hkeys,hplan⟩:=ih (fun r hr=>actual r (by simp [hr]))
     (fun r hr=>pp r (by simp [hr])) (fun r hr=>mm r (by simp [hr]))
   have pact:=actual s (by simp)
   have pproper:=pp s (by simp)
   have pmin:=mm s (by simp)
   cases he : DepthOne.pretest01 (pair t s).1 (pair t s).2 with
   | refused =>
     have hr:=(DepthOne.refused_iff _ _).mp he
     simp [pproper] at hr
   | rejected =>
     refine ⟨.hard (pair t s)::tail,by simpa [jobs,pact,he] using congrArg (Option.map (.hard (pair t s)::·)) ht,
       by simp [hkeys,Job.problem],?_⟩
     intro j hj
     rcases List.mem_cons.mp hj with rfl|hj
     · obtain ⟨F,hF,hcost⟩:=pmin.1
       have hl:=DepthOne.rejected_lower_bound _ _ he F hF
       simpa [Planned,←hcost] using hl
     · exact hplan j hj
   | found c =>
     obtain ⟨ha,hcost,hminimal⟩:=found_minimum_direct _ _ c he
     obtain ⟨F,hF,hopt⟩:=pmin.1
     have hlow:=pmin.2 _ ha
     have hupp:=hminimal F hF
     have hcm : DepthOne.cutCost c=m (pair t s) := by omega
     let j : Job (Tree×Tree) GenericForest.Forest := .resolved (pair t s) (DepthOne.cutCost c) (DepthOne.forest s c)
     refine ⟨j::tail,by simpa [jobs,pact,he,j] using congrArg (Option.map (j::·)) ht,
       by simp [j,hkeys,Job.problem],?_⟩
     intro k hk
     rcases List.mem_cons.mp hk with rfl|hk
     · change DepthOne.cutCost c=m (pair t s) ∧ PairValid m (pair t s) (DepthOne.forest s c) ∧ DepthOne.cutCost c≤1
       exact ⟨hcm,⟨ha,hcost.trans hcm⟩,DepthOne.cutCost_le_one c⟩
     · exact hplan k hk

-- Fixed allocated budget: no global callback correctness or completion needed.
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
   have ht:=planned_tail minimum valid j js hp
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
#print axioms jobs_planned_direct
#print axioms run_sound_fixed
end PaidInstanceForest

-- Author integration type/axiom reports; proof text above is unchanged apart from recorded import edits.
set_option pp.universes true
#check @PaidInstanceForest.found_minimum_direct
#print axioms PaidInstanceForest.found_minimum_direct
#check @PaidInstanceForest.jobs_planned_direct
#print axioms PaidInstanceForest.jobs_planned_direct
#check @PaidInstanceForest.run_complete_fixed
#print axioms PaidInstanceForest.run_complete_fixed
#check @PaidInstanceForest.run_sound_fixed
#print axioms PaidInstanceForest.run_sound_fixed
