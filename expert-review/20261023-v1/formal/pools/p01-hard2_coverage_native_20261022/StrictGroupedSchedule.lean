import OutputGroupBridge
import FullStateSchedule
import Indexing
open RMAF ForestState Universal233 PaidQueries MafScheduler GroupedFullQuery PaidInstanceForest GenericForest
namespace ContactedHard2Survival

theorem feasible_problem_minimum (p : Problem) (H : List (List Nat)) (validH : valid p H) :
 ∃F,valid p F ∧ least p F := by
 have descend : ∀n,∀H,valid p H→cost p H=n→∃F,valid p F ∧ least p F := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
   intro H hH eq
   by_cases minimal : least p H
   · exact ⟨H,hH,minimal⟩
   · have lower : ∃G,valid p G ∧ cost p G<cost p H := by
      apply Classical.byContradiction
      intro absent
      apply minimal
      intro G hG
      have no : ¬cost p G<cost p H := fun h=>absent ⟨G,hG,h⟩
      omega
     obtain ⟨G,hG,lt⟩:=lower
     exact ih (cost p G) (by omega) G hG rfl
 exact descend (cost p H) H validH rfl

theorem strict_forest_callback_sound (ordinary : PaidInstances.OrdinarySolver) (q r : Nat)
 (below : PaidInstances.BelowBudget ordinary q) (strict : r<q) (p : Problem) (c : Nat) (F : List (List Nat))
 (run : callback (PaidInstances.OwnPaid ordinary q) p r=some (c,F)) :
 valid p F ∧ c=cost p F ∧ least p F := by
 obtain ⟨G,runG,eq⟩:=Option.map_eq_some_iff.mp run
 have ee:=Prod.mk.inj eq
 have eqGF : G=F:=ee.2
 subst G
 have sound:=GenericForest.solve_sound (PaidInstances.OwnPaid ordinary q) p.target p.sources r F runG
 refine ⟨sound.1,ee.1.symm,?_⟩
 intro H hH
 by_cases affordable : cost p H≤r
 · obtain ⟨K,runK,leastK⟩:=PaidInstanceForest.forest_completion_obligation r (PaidInstances.OwnPaid ordinary q)
    (PaidInstances.local_ordinary_ih ordinary q r below strict) p.target p.sources H hH affordable
   have eqKF : K=F:=Option.some.inj (runK.symm.trans runG)
   subst K
   exact Nat.sub_le_sub_right leastK _
 · have ownBudget : cost p F≤r:=sound.2
   omega

theorem strict_grouped_schedule (ordinary : PaidInstances.OrdinarySolver) (q r : Nat)
 (below : PaidInstances.BelowBudget ordinary q) (strict : r<q)
 (js : List (Job Problem (List (List Nat)))) (plan : ∀j,j∈js→GroupedFullQuery.Planned j)
 (keysND : (js.map Job.problem).Nodup)
 (H : Problem→List (List Nat)) (supported : ∀j,j∈js→valid j.problem (H j.problem))
 (budget : (js.map (fun j=>cost j.problem (H j.problem))).sum≤r) :
 ∃xs,∃f : Problem→Nat×List (List Nat),
 (schedule (callback (PaidInstances.OwnPaid ordinary q)) r js).answers=some xs ∧
 GroupedFullQuery.Answers js xs ∧ answerCost xs≤(js.map (fun j=>cost j.problem (H j.problem))).sum ∧
 (js.map Job.problem).map f=xs ∧ ∀j,j∈js→valid j.problem (f j.problem).2 ∧ (f j.problem).1=cost j.problem (f j.problem).2 := by
 classical
 letI : DecidableEq Problem:=Classical.typeDecidableEq Problem
 let keys:=js.map Job.problem
 have feasible : ∀p,p∈keys→∃F,valid p F ∧ least p F := by
  intro p hp
  obtain ⟨j,hj,eq⟩:=List.mem_map.mp hp
  subst p
  exact feasible_problem_minimum j.problem (H j.problem) (supported j hj)
 let chosen : Problem→List (List Nat) := fun p=>if h:∃F,valid p F ∧ least p F then h.choose else []
 have chosenValid : ∀p,p∈keys→valid p (chosen p) ∧ least p (chosen p) := by
  intro p hp
  have he:=feasible p hp
  simpa only [chosen,dite_eq_left he] using he.choose_spec
 let m : Problem→Nat:=fun p=>cost p (chosen p)
 let V : Problem→List (List Nat)→Prop:=fun p F=>valid p F ∧ cost p F=m p
 have localKey : ∀j,j∈js→j.problem∈keys:=fun j hj=>List.mem_map.mpr ⟨j,hj,rfl⟩
 have plans : ∀j,j∈js→PaidQueries.Planned m V j := by
  intro j hj
  have hp:=plan j hj
  have minimum:=chosenValid j.problem (localKey j hj)
  cases j with
  | resolved p c F =>
   have eqcost : cost p F=m p := Nat.le_antisymm (hp.2.2.1 _ minimum.1) (minimum.2 _ hp.1)
   exact ⟨hp.2.1.trans eqcost,⟨hp.1,eqcost⟩,hp.2.2.2⟩
  | hard p => exact hp.2 _ minimum.1
 have totalLe : totalMinimum m js≤(js.map (fun j=>cost j.problem (H j.problem))).sum := by
  have sumLe:=sum_map_le' js (fun j=>m j.problem) (fun j=>cost j.problem (H j.problem))
   (fun j hj=>(chosenValid j.problem (localKey j hj)).2 _ (supported j hj))
  have identity : ∀ks : List (Job Problem (List (List Nat))),totalMinimum m ks=(ks.map (fun j=>m j.problem)).sum := by
   intro ks
   induction ks with
   | nil=>rfl
   | cons j ks ih=>simp only [totalMinimum,List.map_cons,List.sum_cons,ih]
  rw [identity js]
  exact sumLe
 have totalBudget : totalMinimum m js≤r:=Nat.le_trans totalLe budget
 let b:=allocated r js
 have bStrict : b<q := by
  have bound : b≤r:=by dsimp [b,allocated];omega
  omega
 have allocation:=feasible_allocation m V js plans r totalBudget
 obtain ⟨xs,runXs⟩:=run_complete_fixed (callback (PaidInstances.OwnPaid ordinary q)) b js (by
  intro p hp
  have kp : p∈keys:=by simpa only [Job.problem] using localKey (.hard p) hp
  have cv:=chosenValid p kp
  obtain ⟨F,runF,_⟩:=PaidInstanceForest.forest_completion_obligation b (PaidInstances.OwnPaid ordinary q)
   (PaidInstances.local_ordinary_ih ordinary q b below bStrict) p.target p.sources (chosen p) cv.1 (allocation p hp)
  exact ⟨(cost p F,F),by simp only [callback,runF,Option.map_some]⟩)
 have answers:=run_sound_fixed m V (callback (PaidInstances.OwnPaid ordinary q)) b js plans (by
  intro p hp c F runF
  have kp : p∈keys:=by simpa only [Job.problem] using localKey (.hard p) hp
  have sound:=strict_forest_callback_sound ordinary q b below bStrict p c F runF
  have cv:=chosenValid p kp
  have eqcost : cost p F=m p:=Nat.le_antisymm (sound.2.2 _ cv.1) (cv.2 _ sound.1)
  exact ⟨sound.2.1.trans eqcost,⟨sound.1,eqcost⟩⟩) xs runXs
 have costXs:=(answers_cost m V js xs answers).1
 have noPrune : ¬r<knownCost js+2*pending js := by have low:=total_lower m V js plans;omega
 have scheduled : (schedule (callback (PaidInstances.OwnPaid ordinary q)) r js).answers=some xs := by
  simp [schedule,noPrune,show (run (callback (PaidInstances.OwnPaid ordinary q)) (allocated r js) js).answers=some xs from runXs,
   show answerCost xs≤r by omega]
 have convert : ∀ks ys,AnswersFor m V ks ys→(∀j,j∈ks→j.problem∈keys)→GroupedFullQuery.Answers ks ys := by
  intro ks ys ah
  induction ah with
  | nil => intro _;exact GroupedFullQuery.Answers.nil
  | @cons j x ks ys hx rest ih =>
   intro keyMap
   have jkey:=keyMap j (by simp)
   exact GroupedFullQuery.Answers.cons ⟨hx.2.1,hx.1.trans hx.2.2.symm,by
    intro G hG
    have low:=(chosenValid j.problem jkey).2 G hG
    have eqcost:=hx.2.2
    dsimp only [m] at eqcost
    omega⟩ (ih (fun k hk=>keyMap k (by simp [hk])))
 have actualAnswers:=convert js xs answers localKey
 obtain ⟨f,fMap,fValid⟩:=answers_indexed m V js xs answers keysND
 refine ⟨xs,f,scheduled,actualAnswers,by omega,fMap,?_⟩
 intro j hj
 have facts:=fValid j hj
 exact ⟨facts.2.1,facts.1.trans facts.2.2.symm⟩
end ContactedHard2Survival

-- Author integration type/axiom reports; proof text above is unchanged apart from recorded import edits.
set_option pp.universes true
#check @ContactedHard2Survival.feasible_problem_minimum
#print axioms ContactedHard2Survival.feasible_problem_minimum
#check @ContactedHard2Survival.strict_forest_callback_sound
#print axioms ContactedHard2Survival.strict_forest_callback_sound
#check @ContactedHard2Survival.strict_grouped_schedule
#print axioms ContactedHard2Survival.strict_grouped_schedule
