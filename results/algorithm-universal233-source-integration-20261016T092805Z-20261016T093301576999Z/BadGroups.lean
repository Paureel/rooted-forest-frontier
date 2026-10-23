import ABCBinding
namespace Universal233.GroupedFullQuery
open RMAF ForestState ForestGroups RestrictionBridge PaidQueries

theorem bad_source_positive (p : Problem) (s : Tree) (hs : s∈p.sources)
 (bad : targetAgrees p.target s (leaves s)=false) (F : Forest) (ha : valid p F) :
 0<cost p F := by
 by_cases pos : 0<cost p F
 · exact pos
 have no : ¬0<cost p F := pos
 have zero : additionalCost p.sources F=0 := by change ¬0<additionalCost p.sources F at no;omega
 obtain ⟨G,hG,_,validG,costG⟩ := ForestPretest01.universal_coverage p.target p.sources F ha (by omega)
 have eg : G=ForestPretest01.unchanged p.sources := ForestPretest01.candidate_zero p.sources G hG (by omega)
 rw [eg] at validG
 have checks := (agrees_parts _ _ _ validG).2.2.2.2 s hs
 simp only [sourceCheck,Bool.and_eq_true] at checks
 have hm : leaves s∈family (leaves s) (ForestPretest01.unchanged p.sources) :=
   (mem_family _ _ _).2 ⟨List.mem_map.2 ⟨s,hs,rfl⟩,List.Subset.refl _⟩
 have good := List.all_eq_true.1 checks.1.2 (leaves s) hm
 simp [bad] at good

/-- A kept original source block whose original restrictions disagree gives a
positive full-group cost, even when other sources in that group overlap on T. -/
theorem kept_bad_group_positive (T S : Tree) (P Q : Forest) (K U : List Nat)
 (hs : (leaves S).Nodup) (ht : (leaves T).Nodup)
 (same : ∀ x,x∈leaves T ↔ x∈leaves S)
 (hP : partitionCheck (leaves S) P=true) (hQ : partitionCheck (labels (some T)) Q=true)
 (hK : K∈P) (hU : U∈Q) (sub : K⊆U) (bad : restrictionAgrees T S K=false) :
 ∀ F,valid (groupProblem (some T) (OutputState.sourceForest S P) U) F →
   0<cost (groupProblem (some T) (OutputState.sourceForest S P) U) F := by
 obtain ⟨s,rs,ls⟩ := OutputState.checked_restrictions S P hs hP K hK
 have proper := OutputState.sourceForest_proper T S P ht hs same hP
 obtain ⟨t,u,eq,ru,localEq,_⟩ := group_target (some T) (OutputState.sourceForest S P) Q proper hQ U hU
 have et : t=T := Option.some.inj eq.symm
 subst t
 have lsU : leaves s⊆U := fun x hx => sub (ls.mem_iff.1 hx)
 have mem : s∈owned (OutputState.sourceForest S P) U := (mem_owned _ _ _).2
   ⟨(OutputState.source_component S P s).2 ⟨K,hK,rs⟩,lsU⟩
 have self : restrict (leaves s) s=some s := restrict_of_contains s _ (fun x hx => List.contains_iff_mem.2 hx)
 have rt : restrict (leaves s) u=restrict K T :=
   (restrict_inside T u U (leaves s) ru lsU).trans
     (KeptParent.restrict_same_members (leaves s) K (fun x => ls.mem_iff) T)
 have localbad : targetAgrees (localTarget (some T) U) s (leaves s)=false := by
   rw [localEq]
   simpa only [targetAgrees,restrictionAgrees,rt,self,rs] using bad
 intro F hF
 exact bad_source_positive _ s mem localbad F hF

theorem one_bad_slot (j : Job Problem Forest) (plan : Planned j)
 (positive : ∀ F,valid j.problem F → 0<cost j.problem F) :
 1≤badSlots [j] := by
 cases j with
 | hard p => simp [badSlots]
 | resolved p c F =>
   have pos := positive F plan.1
   change 0<cost p F at pos
   have nz : c≠0 := by rw [plan.2.1];omega
   simp [badSlots,nz]

theorem prepare_two_bad (p1 p2 : Problem) (js : List (Job Problem Forest))
 (prep : prepare [p1,p2]=some js)
 (pos1 : ∀ F,valid p1 F → 0<cost p1 F)
 (pos2 : ∀ F,valid p2 F → 0<cost p2 F) : 2≤badSlots js := by
 cases h1 : prepareOne p1 with
 | none => simp [prepare,h1] at prep
 | some j1 =>
   cases h2 : prepareOne p2 with
   | none => simp [prepare,h1,h2] at prep
   | some j2 =>
     have eq : js=[j1,j2] := by simpa [prepare,h1,h2] using prep.symm
     subst js
     have spec1 := prepareOne_spec p1 j1 h1
     have spec2 := prepareOne_spec p2 j2 h2
     have hb1 := one_bad_slot j1 spec1.2 (by simpa [spec1.1] using pos1)
     have hb2 := one_bad_slot j2 spec2.2 (by simpa [spec2.1] using pos2)
     have add : badSlots [j1,j2]=badSlots [j1]+badSlots [j2] := by
       cases j1 <;> simp [badSlots]
     omega

theorem kept_AB_C_badSlots (T S : Tree) (P : Forest) (A B C : List Nat)
 (hs : (leaves S).Nodup) (ht : (leaves T).Nodup)
 (same : ∀ x,x∈leaves T ↔ x∈leaves S)
 (hP : partitionCheck (leaves S) P=true)
 (hp : partitionCheck (leaves S) [A,B,C]=true)
 (keptA : A∈P) (keptC : C∈P)
 (badA : restrictionAgrees T S A=false) (badC : restrictionAgrees T S C=false)
 (js : List (Job Problem Forest))
 (prep : prepare (groupProblems (some T) (OutputState.sourceForest S P) [A++B,C])=some js) :
 2≤badSlots js := by
 have hQ : partitionCheck (labels (some T)) [A++B,C]=true :=
   (partition_labels_congr _ _ _ same).2 (merge_ab_partition _ A B C hp)
 apply prepare_two_bad _ _ js prep
 · exact kept_bad_group_positive T S P [A++B,C] A (A++B) hs ht same hP hQ keptA (by simp)
     (fun x hx => List.mem_append_left B hx) badA
 · exact kept_bad_group_positive T S P [A++B,C] C C hs ht same hP hQ keptC (by simp)
     (List.Subset.refl _) badC
end Universal233.GroupedFullQuery
