import EdgeClade
open RMAF VertexGeometry ForestState ForestGroups RestrictionBridge OutputState Universal233
namespace ContactedHard2Survival

theorem parent_family_perm (T S : Tree) (A B C : List Nat) (H : List (List Nat))
 (proper : DepthOne.proper T S=true) (part : partitionCheck (leaves S) [A,B,C]=true)
 (agree : agreement T S H=true) (ref : VertexGeometry.Refines H [A,B,C]) :
 (family A H).flatten.Perm A := by
 have pp:=IndependentReconstruction.proper_parts proper
 have targetPart : partitionCheck (leaves T) [A,B,C]=true :=
  (partition_labels_congr (leaves S) (leaves T) _ (fun _=>pp.2.2.mem_iff.symm)).mp part
 obtain ⟨u,restriction,perm⟩:=checked_restrictions T [A,B,C] pp.1 targetPart A (by simp)
 have member : u∈sourceForest T [A,B,C] := by
  apply List.mem_filterMap.mpr
  exact ⟨A,by simp,restriction⟩
 have material:=checked_materialization T [A,B,C] pp.1 targetPart
 obtain ⟨D,dP,_,_,ndu,_⟩:=material.2.2 u member
 have familyCheck:=local_partition T u A H [A,B,C] restriction (by
  have a:=agree;simp only [agreement,Bool.and_eq_true] at a;exact a.1.1.1.1) targetPart ref (by simp)
 exact (IndependentCommon.flatten_from_partition _ (family A H) ndu familyCheck).trans perm

theorem parent_of_label (L : List Nat) (P : List (List Nat)) (part : partitionCheck L P=true)
 (H : List (List Nat)) (ref : VertexGeometry.Refines H P) (A K : List Nat) (aP : A∈P)
 (kH : K∈H) (x : Nat) (xK : x∈K) (xA : x∈A) : K⊆A := by
 obtain ⟨U,uP,sub⟩:=ref K kH
 have same:=ForestGroups.group_unique L P part U A uP aP x (sub x xK) xA
 rw [same] at sub
 exact sub

theorem collapse_refines (A B C : List Nat) (H : List (List Nat)) (ref : VertexGeometry.Refines H [A,B,C]) :
 VertexGeometry.Refines (collapseParent A H) [A,B,C] := by
 intro K member
 rcases List.mem_cons.mp member with eq|rest
 · subst K;exact ⟨A,by simp,fun _ hx=>hx⟩
 · exact ref K (List.mem_filter.mp rest).1
end ContactedHard2Survival

-- Author integration type/axiom reports; proof text above is unchanged apart from recorded import edits.
set_option pp.universes true
#check @ContactedHard2Survival.parent_family_perm
#print axioms ContactedHard2Survival.parent_family_perm
#check @ContactedHard2Survival.parent_of_label
#print axioms ContactedHard2Survival.parent_of_label
#check @ContactedHard2Survival.collapse_refines
#print axioms ContactedHard2Survival.collapse_refines
