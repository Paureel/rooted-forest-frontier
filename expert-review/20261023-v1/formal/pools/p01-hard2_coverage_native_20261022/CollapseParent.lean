import OriginalFourPaidCases
open RMAF ForestState ForestGroups RestrictionBridge Universal233
namespace ContactedHard2Survival

def outsideParent (A : List Nat) (F : List (List Nat)) := F.filter (fun K=>!contained K A)
def collapseParent (A : List Nat) (F : List (List Nat)) := A::outsideParent A F

theorem move_head_append {α : Type} (a : α) (L R : List α) : (a::(L++R)).Perm (L++a::R) := by
 induction L with
 | nil=>exact List.Perm.refl _
 | cons x xs ih=>exact (List.Perm.swap _ _ _).trans (List.Perm.cons x ih)

theorem filter_complement_perm {α : Type} (p : α→Bool) (L : List α) :
 L.Perm (L.filter p++L.filter (fun a=>!p a)) := by
 induction L with
 | nil=>exact List.Perm.refl _
 | cons x xs ih=>
  cases eq : p x with
  | true=>simpa only [List.filter_cons,eq,Bool.not_true,ite_true,Bool.false_eq_true,ite_false,List.cons_append] using List.Perm.cons x ih
  | false=>
   have result:=(List.Perm.cons x ih).trans (move_head_append x (xs.filter p) (xs.filter (fun a=>!p a)))
   simpa only [List.filter_cons,eq,Bool.not_false,ite_true,Bool.false_eq_true,ite_false] using result

theorem collapse_flatten (A : List Nat) (F : List (List Nat)) (familyPerm : (family A F).flatten.Perm A) :
 (collapseParent A F).flatten.Perm F.flatten := by
 have split:=filter_complement_perm (fun K=>contained K A) F
 have flat:=split.flatten
 rw [List.flatten_append] at flat
 have replacement : ((family A F).flatten++(outsideParent A F).flatten).Perm (A++(outsideParent A F).flatten) :=
  List.Perm.append_right _ familyPerm
 exact (flat.trans replacement).symm

theorem collapse_nonempty (A : List Nat) (F : List (List Nat)) (an : A≠[]) (fn : ∀K,K∈F→K≠[]) :
 ∀K,K∈collapseParent A F→K≠[] := by
 intro K member
 rcases List.mem_cons.mp member with eq|rest
 · subst K;exact an
 · exact fn K (List.mem_filter.mp rest).1

theorem collapse_count (A : List Nat) (F : List (List Nat)) (two : 2≤(family A F).length) :
 (collapseParent A F).length+1≤F.length := by
 have len:=(filter_complement_perm (fun K=>contained K A) F).length_eq
 change F.length=(family A F++outsideParent A F).length at len
 simp only [List.length_append] at len
 change (outsideParent A F).length+1+1≤F.length
 omega

theorem collapse_agreement (T S : Tree) (A : List Nat) (F : List (List Nat))
 (proper : DepthOne.proper T S=true) (agree : agreement T S F=true)
 (an : A≠[]) (good : restrictionAgrees T S A=true) (familyPerm : (family A F).flatten.Perm A)
 (targetClear : ∀K,K∈outsideParent A F→disjointVertices (minimalVertices A T) (minimalVertices K T)=true)
 (sourceClear : ∀K,K∈outsideParent A F→disjointVertices (minimalVertices A S) (minimalVertices K S)=true) :
 agreement T S (collapseParent A F)=true := by
 have pp:=IndependentReconstruction.proper_parts proper
 have old:=agree;simp only [agreement,Bool.and_eq_true] at old
 have perm:=collapse_flatten A F familyPerm
 have ne:=collapse_nonempty A F an (agreement_nonempty T S F agree)
 have pt:=IndependentCommon.partition_from_flatten _ _ pp.1 ne
  (perm.trans (IndependentCommon.flatten_from_partition _ F pp.1 old.1.1.1.1))
 have ps:=IndependentCommon.partition_from_flatten _ _ pp.2.1 ne
  (perm.trans (IndependentCommon.flatten_from_partition _ F pp.2.1 old.1.1.1.2))
 have shapes : (collapseParent A F).all (restrictionAgrees T S)=true := by
  apply List.all_eq_true.mpr
  intro K member
  rcases List.mem_cons.mp member with eq|rest
  · subst K;exact good
  · exact List.all_eq_true.mp old.1.1.2 K (List.mem_filter.mp rest).1
 have target : pairwiseEmbeddings T (collapseParent A F)=true := by
  change (_ && _)=true
  simp only [Bool.and_eq_true]
  exact ⟨List.all_eq_true.mpr targetClear,IndependentGeometry.pairwise_filter T F _ old.1.2⟩
 have source : pairwiseEmbeddings S (collapseParent A F)=true := by
  change (_ && _)=true
  simp only [Bool.and_eq_true]
  exact ⟨List.all_eq_true.mpr sourceClear,IndependentGeometry.pairwise_filter S F _ old.2⟩
 simpa only [agreement,Bool.and_eq_true] using (show (((_ ∧ _) ∧ _) ∧ _) ∧ _ from ⟨⟨⟨⟨pt,ps⟩,shapes⟩,target⟩,source⟩)
end ContactedHard2Survival

-- Author integration type/axiom reports; proof text above is unchanged apart from recorded import edits.
set_option pp.universes true
#check @ContactedHard2Survival.move_head_append
#print axioms ContactedHard2Survival.move_head_append
#check @ContactedHard2Survival.filter_complement_perm
#print axioms ContactedHard2Survival.filter_complement_perm
#check @ContactedHard2Survival.collapse_flatten
#print axioms ContactedHard2Survival.collapse_flatten
#check @ContactedHard2Survival.collapse_nonempty
#print axioms ContactedHard2Survival.collapse_nonempty
#check @ContactedHard2Survival.collapse_count
#print axioms ContactedHard2Survival.collapse_count
#check @ContactedHard2Survival.collapse_agreement
#print axioms ContactedHard2Survival.collapse_agreement
