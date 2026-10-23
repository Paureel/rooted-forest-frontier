-- Source-guided replacement. Legacy forest minimum theorem is never applied.
import OriginalCgoodCoverResume
import ForestPretest01
import ForestCoverage
import ForestPretestSemantics
import FullStateJobs
namespace Universal233.GroupedFullQuery
end Universal233.GroupedFullQuery
open RMAF ForestState Universal233 Universal233.PaidQueries Universal233.GroupedFullQuery
set_option autoImplicit false
namespace ContactedHard2Survival

theorem forest_found_minimum_direct (T : Option Tree) (ss : List Tree) (F : List (List Nat))
 (found : ForestPretest01.pretest01 T ss=.found F) :
 agrees T ss F=true ∧ additionalCost ss F≤1 ∧
 ∀G,agrees T ss G=true→additionalCost ss F≤additionalCost ss G := by
 obtain ⟨proper,member,agree,small,least⟩:=ForestPretest01.found_spec T ss F found
 refine ⟨agree,small,?_⟩
 intro G agreeG
 by_cases cheap : additionalCost ss G≤1
 · obtain ⟨H,memberH,_,agreeH,costH⟩:=ForestPretest01.universal_coverage T ss G agreeG cheap
   have bound:=least H memberH agreeH
   omega
 · omega

theorem prepareOne_spec_direct (p : Problem) (j : Job Problem (List (List Nat))) (h : prepareOne p=some j) :
 j.problem=p ∧ GroupedFullQuery.Planned j := by
 cases step : ForestPretest01.pretest01 p.target p.sources with
 | refused=>simp only [prepareOne,step] at h;cases h
 | found F=>
  have same : (.resolved p (cost p F) F : Job Problem (List (List Nat)))=j:=Option.some.inj (by unfold prepareOne at h;rw [step] at h;exact h)
  subst j
  obtain ⟨agree,cheap,least⟩:=forest_found_minimum_direct p.target p.sources F step
  exact ⟨rfl,agree,rfl,least,cheap⟩
 | rejected=>
  have same : (.hard p : Job Problem (List (List Nat)))=j:=Option.some.inj (by unfold prepareOne at h;rw [step] at h;exact h)
  subst j
  exact ⟨rfl,ForestPretest01.rejected_lower_bound _ _ step⟩

theorem common_prepare_spec (ps : List Problem) (js : List (Job Problem (List (List Nat))))
 (h : prepare ps=some js) : js.map Job.problem=ps ∧ ∀j,j∈js→GroupedFullQuery.Planned j := by
 induction ps generalizing js with
 | nil=>
  have same : []=js:=Option.some.inj h
  subst js
  exact ⟨rfl,by intro j member;cases member⟩
 | cons p ps ih=>
  change (do let j ← prepareOne p;let tail ← prepare ps;pure (j::tail))=some js at h
  cases one : prepareOne p with
  | none=>simp only [one,Option.bind_none] at h;cases h
  | some j=>
   cases rest : prepare ps with
   | none=>simp only [one,rest,Option.bind_some,Option.bind_none] at h;cases h
   | some tail=>
    have same : j::tail=js:=Option.some.inj (by rw [one,rest] at h;exact h)
    subst js
    obtain ⟨key,planned⟩:=prepareOne_spec_direct p j one
    obtain ⟨keys,planTail⟩:=ih tail rest
    refine ⟨?_,?_⟩
    · change j.problem::tail.map Job.problem=p::ps
      exact (congrArg (fun x=>x::tail.map (@Job.problem Problem (List (List Nat)))) key).trans (congrArg (List.cons p) keys)
    ·
     intro k member
     rcases List.mem_cons.mp member with eq|member
     · subst k;exact planned
     · exact planTail k member

theorem prepareOne_exists_direct (p : Problem) (proper : ForestState.proper p.target p.sources=true) :
 ∃j,prepareOne p=some j := by
 cases step : ForestPretest01.pretest01 p.target p.sources with
 | refused=>
  unfold ForestPretest01.pretest01 at step
  rw [proper] at step
  cases best : RMAF.best (additionalCost p.sources) (agrees p.target p.sources) (ForestPretest01.candidates p.sources) <;>simp_all only [ForestPretest01.pretest01.match_1,ite_true] <;>cases step
 | found F=>exact ⟨.resolved p (cost p F) F,by unfold prepareOne;rw [step] <;> rfl⟩
 | rejected=>exact ⟨.hard p,by unfold prepareOne;rw [step] <;> rfl⟩

theorem common_prepare_exists (ps : List Problem)
 (proper : ∀p,p∈ps→ForestState.proper p.target p.sources=true) : ∃js,prepare ps=some js := by
 induction ps with
 | nil=>exact ⟨[],rfl⟩
 | cons p ps ih=>
  obtain ⟨j,one⟩:=prepareOne_exists_direct p (proper p List.mem_cons_self)
  obtain ⟨tail,rest⟩:=ih (fun p member=>proper p (List.mem_cons_of_mem _ member))
  refine ⟨j::tail,?_⟩
  change (do let k ← prepareOne p;let ks ← prepare ps;pure (k::ks))=some (j::tail)
  rw [one,rest];rfl
end ContactedHard2Survival

-- Author integration type/axiom reports; proof text above is unchanged apart from recorded import edits.
set_option pp.universes true
#check @ContactedHard2Survival.forest_found_minimum_direct
#print axioms ContactedHard2Survival.forest_found_minimum_direct
#check @ContactedHard2Survival.prepareOne_spec_direct
#print axioms ContactedHard2Survival.prepareOne_spec_direct
#check @ContactedHard2Survival.common_prepare_spec
#print axioms ContactedHard2Survival.common_prepare_spec
#check @ContactedHard2Survival.prepareOne_exists_direct
#print axioms ContactedHard2Survival.prepareOne_exists_direct
#check @ContactedHard2Survival.common_prepare_exists
#print axioms ContactedHard2Survival.common_prepare_exists
