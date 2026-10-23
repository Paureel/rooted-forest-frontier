import RetainedSourceTemplate
open RMAF VertexGeometry ForestState ForestGroups RestrictionBridge OutputState Universal233
namespace ContactedHard2Survival

theorem materialized_owned_count (S : Tree) (P : List (List Nat)) (A : List Nat)
 (actual : ∀U,U∈P→∃s,restrict U S=some s ∧ (leaves s).Perm U) :
 (owned (sourceForest S P) A).length=(family A P).length := by
 induction P with
 | nil=>rfl
 | cons U P ih=>
  obtain ⟨s,source,labels⟩:=actual U List.mem_cons_self
  have tail:=ih (fun V hv=>actual V (List.mem_cons_of_mem U hv))
  have condition : contained (leaves s) A=contained U A := by
   apply Bool.eq_iff_iff.mpr
   constructor
   · intro yes
     apply (contained_iff U A).mpr
     intro x hx
     exact (contained_iff (leaves s) A).mp yes (labels.mem_iff.mpr hx)
   · intro yes
     apply (contained_iff (leaves s) A).mpr
     intro x hx
     exact (contained_iff U A).mp yes (labels.mem_iff.mp hx)
  have head : sourceForest S (U::P)=s::sourceForest S P := by
   delta sourceForest
   simp only [List.filterMap_cons,source]
  rw [head]
  change (List.filter (fun t=>contained (leaves t) A) (s::sourceForest S P)).length=
   (List.filter (fun V=>contained V A) (U::P)).length
  simp only [List.filter_cons,condition]
  change (List.filter (fun t=>contained (leaves t) A) (sourceForest S P)).length=
   (List.filter (fun V=>contained V A) P).length at tail
  cases contained U A <;>simp only [Bool.false_eq_true,ite_false,ite_true,List.length_cons] <;>omega

theorem whole_parent_family_one (L : List Nat) (P Q J : List (List Nat)) (A : List Nat)
 (nd : L.Nodup) (partP : partitionCheck L P=true) (partQ : partitionCheck L Q=true)
 (refP : VertexGeometry.Refines P Q) (refJ : VertexGeometry.Refines J P) (aQ : A∈Q) (aJ : A∈J) (neA : A≠[]) :
 (family A P).length=1 := by
 obtain ⟨U,uP,aSub⟩:=refJ A aJ
 obtain ⟨V,vQ,uSub⟩:=refP U uP
 obtain ⟨x,xA⟩:=List.exists_mem_of_ne_nil A neA
 have same:=group_unique L Q partQ V A vQ aQ x (uSub _ (aSub _ xA)) xA
 subst V
 have member : U∈family A P:=List.mem_filter.mpr ⟨uP,contained_true_of_subset U A uSub⟩
 have unique : ∀K,K∈family A P→K=U := by
  intro K memberK
  have fields:=List.mem_filter.mp memberK
  have sub:K⊆A:=(contained_iff K A).mp fields.2
  obtain ⟨y,yK⟩:=List.exists_mem_of_ne_nil K (partition_nonempty_member L P partP K fields.1)
  exact group_unique L P partP K U fields.1 uP y yK (aSub _ (sub yK))
 have flat:=(IndependentCommon.flatten_from_partition L P nd partP).symm.nodup nd
 have pND:=IndependentPaid.blocks_nodup P flat (partition_nonempty_member L P partP)
 have familyND : (family A P).Nodup:=List.Pairwise.filter _ pND
 have upper:=familyND.length_le_of_subset (l₂:=[U]) (by
  intro K memberK
  simp only [List.mem_cons,List.not_mem_nil,or_false]
  exact unique K memberK)
 have lower:=List.length_pos_of_mem member
 simp only [List.length_cons,List.length_nil] at upper
 omega

theorem bad_parent_family_two (T S : Tree) (P F : List (List Nat)) (A : List Nat)
 (proper : DepthOne.proper T S=true) (part : partitionCheck (leaves S) P=true)
 (agree : agreement T S F=true) (ref : VertexGeometry.Refines F P) (aP : A∈P)
 (bad : restrictionAgrees S T A=false) : 2≤(family A F).length := by
 have perm:=parent_family_perm_any T S P F proper part agree ref A aP
 have neA:=partition_nonempty_member _ _ part A aP
 have lower:=flatten_perm_nonempty_length _ _ perm neA
 cases h : family A F with
 | nil=>simp only [h,List.length_nil] at lower;omega
 | cons K rest=>
  cases rest with
  | nil=>
   have kFamily : K∈family A F:=by rw [h];exact List.mem_cons_self
   have kF:=(List.mem_filter.mp kFamily).1
   have checks:=agree
   simp only [agreement,Bool.and_eq_true] at checks
   have goodK:=ContactedHard2DP.restriction_good_swap (List.all_eq_true.mp checks.1.1.2 K kF)
   have permK : K.Perm A:=by simpa only [h,List.flatten_cons,List.flatten_nil,List.append_nil] using perm
   have masks : ∀x,K.contains x=A.contains x := by
    intro x
    apply Bool.eq_iff_iff.mpr
    simpa only [List.contains_iff_mem] using permK.mem_iff
   have goodA : restrictionAgrees S T A=true:=by rw [←ContactedHard2DP.restriction_mask S T K A masks];exact goodK
   exact False.elim (Bool.noConfusion (bad.symm.trans goodA))
  | cons J rest=>simp only [List.length_cons];omega
end ContactedHard2Survival

-- Author integration type/axiom reports; proof text above is unchanged apart from recorded import edits.
set_option pp.universes true
#check @ContactedHard2Survival.materialized_owned_count
#print axioms ContactedHard2Survival.materialized_owned_count
#check @ContactedHard2Survival.whole_parent_family_one
#print axioms ContactedHard2Survival.whole_parent_family_one
#check @ContactedHard2Survival.bad_parent_family_two
#print axioms ContactedHard2Survival.bad_parent_family_two
