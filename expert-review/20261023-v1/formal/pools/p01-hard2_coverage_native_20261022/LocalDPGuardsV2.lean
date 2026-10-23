-- Actual A++B local state: derive allGood from original consumed source checks.
import LocalDPCallControls
open RMAF ForestState ForestGroups RestrictionBridge OutputState Universal233
open IndependentGeometry IndependentReconstruction
namespace ContactedHard2DP

theorem restriction_good_swap {T S : Tree} {B : List Nat}
 (h : restrictionAgrees T S B=true) : restrictionAgrees S T B=true := by
 unfold restrictionAgrees at h ⊢
 cases l : restrict B T <;> cases r : restrict B S <;> simp [l,r] at h ⊢
 exact iso_same (iso_sym (same_iso h))

theorem restriction_mask (T S : Tree) (A B : List Nat) (eq : ∀x,A.contains x=B.contains x) :
 restrictionAgrees T S A=restrictionAgrees T S B := by
 unfold restrictionAgrees
 rw [ContactedClade.restrict_ext T A B eq,ContactedClade.restrict_ext S A B eq]

theorem merge_first_two_check (L A B C : List Nat) (part : partitionCheck L [A,B,C]=true) :
 partitionCheck L [A++B,C]=true := by
 have neA:=checked_nonempty L [A,B,C] part A List.mem_cons_self
 have neC:=checked_nonempty L [A,B,C] part C (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
 have cGood : (!C.isEmpty)=true := by
  cases C with
  | nil => exact False.elim (neC rfl)
  | cons x C => rfl
 simp only [partitionCheck,Bool.and_eq_true] at part ⊢
 refine ⟨⟨?_,?_⟩,?_⟩
 · cases A with
   | nil => exact False.elim (neA rfl)
   | cons a A => simpa only [List.all_cons,List.all_nil,List.cons_append,List.isEmpty_cons,Bool.not_false,Bool.true_and,Bool.and_true] using cGood
 · simpa only [List.flatten_cons,List.flatten_nil,List.append_nil,List.append_assoc] using part.1.2
 · simpa only [List.flatten_cons,List.flatten_nil,List.append_nil,List.append_assoc] using part.2

theorem materialized_good_local {T S s t : Tree} {D U : List Nat}
 (source : restrict D S=some s) (target : restrict U T=some t)
 (sub : D⊆U) (labels : (leaves s).Perm D) (good : restrictionAgrees S T D=true) :
 targetAgrees (some t) s (leaves s)=true := by
 have mask : ∀x,(leaves s).contains x=D.contains x := by
  intro x
  apply Bool.eq_iff_iff.2
  simp only [List.contains_iff_mem]
  exact labels.mem_iff
 have global : restrictionAgrees S T (leaves s)=true := by
  rw [restriction_mask S T (leaves s) D mask]
  exact good
 have sourceGlobal : restrictionAgrees T s (leaves s)=true := by
  rw [FreshResidual.materialized_restriction source (fun x hx=>labels.mem_iff.1 hx)]
  exact restriction_good_swap global
 have targetLocal : restrictionAgrees s t (leaves s)=true := by
  rw [FreshResidual.materialized_restriction target (fun x hx=>sub (labels.mem_iff.1 hx))]
  exact restriction_good_swap sourceGlobal
 exact restriction_good_swap targetLocal

theorem literal_pair_allGood (T S : Tree) (A B C : List Nat)
 (proper : DepthOne.proper T S=true) (part : partitionCheck (leaves S) [A,B,C]=true)
 (emb : pairwiseEmbeddings S [A,B,C]=true)
 (goodA : restrictionAgrees S T A=true) (goodB : restrictionAgrees S T B=true) :
 AllGoodDP.allGood (localTarget (some T) (A++B)) (owned (sourceForest S [A,B,C]) (A++B))=true := by
 let ss:=sourceForest S [A,B,C]
 let Q:List (List Nat):=[A++B,C]
 have pparts:=IndependentReconstruction.proper_parts proper
 have material:=checked_materialization S [A,B,C] pparts.2.1 part
 have globalProper : ForestState.proper (some T) ss=true :=
   (FreshResidual.residual_transfer_scope.1 T S [A,B,C] [] proper part emb).2.1
 have qS : partitionCheck (leaves S) Q=true := merge_first_two_check _ _ _ _ part
 have qT : partitionCheck (ForestState.labels (some T)) Q=true :=
   (partition_labels_congr (leaves S) (leaves T) Q (fun x=>pparts.2.2.mem_iff.symm)).1 qS
 have ownership : Owns ss Q := by
  intro s member
  obtain ⟨D,dP,_,perm,_,_⟩:=material.2.2 s member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at dP
  rcases dP with eq|eq|eq <;> subst D
  · exact ⟨A++B,List.mem_cons_self,fun x hx=>List.mem_append_left _ (perm.mem_iff.1 hx)⟩
  · exact ⟨A++B,List.mem_cons_self,fun x hx=>List.mem_append_right _ (perm.mem_iff.1 hx)⟩
  · exact ⟨C,List.mem_cons_of_mem _ List.mem_cons_self,fun x hx=>perm.mem_iff.1 hx⟩
 have localProper:=ForestGroups.local_proper (some T) ss Q globalProper qT ownership (A++B) List.mem_cons_self
 obtain ⟨t,u,ht,hu,hlocal,_⟩:=ForestGroups.group_target (some T) ss Q globalProper qT (A++B) List.mem_cons_self
 have eq : t=T := (Option.some.inj ht).symm
 subst t
 have flat := (checked_flatten_perm (leaves S) [A,B,C] pparts.2.1 part).symm.nodup pparts.2.1
 have nd : ((A++B)++C).Nodup := by
  simpa only [List.flatten_cons,List.flatten_nil,List.append_nil,List.append_assoc] using flat
 have clear : ∀x,x∈A++B→x∈C→False := by
  intro x hAB hC
  exact (List.nodup_append.1 nd).2.2 x hAB x hC rfl
 unfold AllGoodDP.allGood
 simp only [Bool.and_eq_true]
 refine ⟨localProper,List.all_eq_true.2 ?_⟩
 intro s member
 have srcmem : s∈ss := (List.mem_filter.1 member).1
 have subU : leaves s⊆A++B := (contained_iff _ _).1 (List.mem_filter.1 member).2
 obtain ⟨D,dP,source,labels,_,_⟩:=material.2.2 s srcmem
 rw [hlocal]
 simp only [List.mem_cons,List.not_mem_nil,or_false] at dP
 rcases dP with eq|eq|eq <;> subst D
 · exact materialized_good_local source hu (fun x hx=>List.mem_append_left _ hx) labels goodA
 · exact materialized_good_local source hu (fun x hx=>List.mem_append_right _ hx) labels goodB
 · obtain ⟨x,hx⟩:=List.exists_mem_of_ne_nil C (checked_nonempty _ _ part C (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))
   exact False.elim (clear x (subU (labels.mem_iff.2 hx)) hx)
end ContactedHard2DP

-- Author integration type/axiom reports; proof text above is unchanged apart from recorded import edits.
set_option pp.universes true
#check @ContactedHard2DP.restriction_good_swap
#print axioms ContactedHard2DP.restriction_good_swap
#check @ContactedHard2DP.restriction_mask
#print axioms ContactedHard2DP.restriction_mask
#check @ContactedHard2DP.merge_first_two_check
#print axioms ContactedHard2DP.merge_first_two_check
#check @ContactedHard2DP.materialized_good_local
#print axioms ContactedHard2DP.materialized_good_local
#check @ContactedHard2DP.literal_pair_allGood
#print axioms ContactedHard2DP.literal_pair_allGood
