import SplitColors
open RMAF VertexGeometry ForestState ForestGroups RestrictionBridge Universal233
namespace ContactedHard2Survival

theorem contained_true_of_subset (K A : List Nat) (sub : K⊆A) : contained K A=true := by
 apply List.all_eq_true.mpr
 intro x hx;exact List.contains_iff_mem.mpr (sub hx)

theorem outside_parent_owner (A B C : List Nat) (H : List (List Nat))
 (ref : VertexGeometry.Refines H [A,B,C]) (k : List Nat) (member : k∈outsideParent A H) : k⊆B ∨ k⊆C := by
 have kh:=List.mem_filter.mp member
 obtain ⟨D,dP,sub⟩:=ref k kh.1
 simp only [List.mem_cons,List.not_mem_nil,or_false] at dP
 rcases dP with eq|eq|eq <;>subst D
 · have yes:=contained_true_of_subset k A sub
   have no:=kh.2
   simp only [yes,Bool.not_true,Bool.false_eq_true] at no
 · exact Or.inl sub
 · exact Or.inr sub

theorem two_distinct_members_length {α : Type} (L : List α) (A B : α) (a : A∈L) (b : B∈L) (ne : A≠B) :
 2≤L.length := by
 cases L with
 | nil=>simp at a
 | cons C rest=>
  cases rest with
  | nil=>
   have ac : A=C := by simpa only [List.mem_cons,List.not_mem_nil,or_false] using a
   have bc : B=C := by simpa only [List.mem_cons,List.not_mem_nil,or_false] using b
   exact False.elim (ne (ac.trans bc.symm))
  | cons D rest=>simp only [List.length_cons];omega

theorem monochrome_family_two (T S : Tree) (A B C D : List Nat) (H : List (List Nat))
 (proper : DepthOne.proper T S=true) (part : partitionCheck (leaves S) [A,B,C]=true)
 (agree : agreement T S H=true) (ref : VertexGeometry.Refines H [A,B,C])
 (mono : ∀K,K∈H→LabelMonochromatic (sideColor D) K)
 (x y : Nat) (xA : x∈A) (yA : y∈A) (xd : x∈D) (yd : y∉D) : 2≤(family A H).length := by
 have pp:=IndependentReconstruction.proper_parts proper
 have labels:=partition_member_labels _ _ part A (by simp)
 have ax : x∈leaves T:=pp.2.2.mem_iff.mpr (labels x xA)
 have ay : y∈leaves T:=pp.2.2.mem_iff.mpr (labels y yA)
 have targetPart:=by
  have a:=agree;simp only [agreement,Bool.and_eq_true] at a;exact a.1.1.1.1
 obtain ⟨K,kH,xK⟩:=checked_covers (leaves T) H targetPart ax
 obtain ⟨L,lH,yL⟩:=checked_covers (leaves T) H targetPart ay
 have ka:=parent_of_label _ _ part H ref A K (by simp) kH x xK xA
 have la:=parent_of_label _ _ part H ref A L (by simp) lH y yL yA
 have km : K∈family A H:=List.mem_filter.mpr ⟨kH,contained_true_of_subset K A ka⟩
 have lm : L∈family A H:=List.mem_filter.mpr ⟨lH,contained_true_of_subset L A la⟩
 apply two_distinct_members_length _ K L km lm
 intro eq
 subst L
 have impossible:=mono K kH x y xK yL
 simp only [sideColor,ite_eq_left xd,ite_eq_right yd] at impossible
 cases impossible
end ContactedHard2Survival

-- Author integration type/axiom reports; proof text above is unchanged apart from recorded import edits.
set_option pp.universes true
#check @ContactedHard2Survival.contained_true_of_subset
#print axioms ContactedHard2Survival.contained_true_of_subset
#check @ContactedHard2Survival.outside_parent_owner
#print axioms ContactedHard2Survival.outside_parent_owner
#check @ContactedHard2Survival.two_distinct_members_length
#print axioms ContactedHard2Survival.two_distinct_members_length
#check @ContactedHard2Survival.monochrome_family_two
#print axioms ContactedHard2Survival.monochrome_family_two
