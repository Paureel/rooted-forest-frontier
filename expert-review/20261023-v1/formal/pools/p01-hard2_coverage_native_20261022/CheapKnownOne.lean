import CheapLocalGeometry
open RMAF VertexGeometry ForestState ForestGroups RestrictionBridge OutputState Universal233 Universal233.CoreProgram
namespace ContactedHard2Survival

theorem checked_parent_family_positive (L : List Nat) (Q P : List (List Nat)) (A : List Nat)
 (parents : partitionCheck L Q=true) (part : partitionCheck L P=true)
 (ref : VertexGeometry.Refines P Q) (aQ : A∈Q) : 1≤(family A P).length := by
 obtain ⟨x,xA⟩:=List.exists_mem_of_ne_nil A (partition_nonempty_member L Q parents A aQ)
 obtain ⟨K,kP,xK⟩:=checked_covers L P part (partition_member_labels L Q parents A aQ x xA)
 have sub:=parent_of_label L Q parents P ref A K aQ kP x xK xA
 exact List.length_pos_of_mem ((family_members_fresh K A P).mpr ⟨kP,sub⟩)

theorem probe_source_refines (T S : Tree) (A B C : List Nat) (p : RMAF.Vertex) (P : List (List Nat))
 (parentsSwap : partitionCheck (leaves S) [B,A,C]=true) (nd : (leaves S).Nodup)
 (part : partitionCheck (leaves S) P=true)
 (mono : ∀K,K∈P→LabelMonochromatic (edgeCheapColor A B (PairGeometry.descendants T p)) K) :
 VertexGeometry.Refines P [A,B,C] := by
 have swapped:=tagged_partition_refines S B A C (fun _=>0) (sideColor (PairGeometry.descendants T p)) (fun _=>0)
  P nd parentsSwap part mono
 intro K kP
 obtain ⟨U,uQ,sub⟩:=swapped K kP
 exact ⟨U,(List.Perm.swap B A [C]).mem_iff.mpr uQ,sub⟩

theorem cheap_probe_knownOne (T S : Tree) (A B C : List Nat) (e : RMAF.Vertex×RMAF.Vertex)
 (proper : DepthOne.proper T S=true)
 (parents : partitionCheck (leaves S) [A,B,C]=true) (parentsSwap : partitionCheck (leaves S) [B,A,C]=true)
 (edge : e∈PairGeometry.edges T) (x y : Nat) (xA : x∈A) (yA : y∈A)
 (xd : x∈PairGeometry.descendants T e.2) (yn : y∉PairGeometry.descendants T e.2)
 (o : Output) (member : o∈(generate S (edgeCheapColor A B (PairGeometry.descendants T e.2)) 3).outputs)
 (yesGood : restrictionAgrees S T (BinaryCheap.ay A (PairGeometry.descendants T e.2))=true)
 (noGood : restrictionAgrees S T (BinaryCheap.an A (PairGeometry.descendants T e.2))=true)
 (badA : restrictionAgrees S T A=false) : ∃known,BothBad.knownOne T S A=some known := by
 have pp:=IndependentReconstruction.proper_parts proper
 let D:=PairGeometry.descendants T e.2
 have scope:=cheap_probe_saturation S A B C D parents pp.2.1 x y xA yA xd yn o member
 have mono:=CutRealization.generate_monochromatic S (edgeCheapColor A B D) 3 o member
 have ref:=probe_source_refines T S A B C e.2 o.partition parentsSwap pp.2.1 scope.2.1 mono
 have fibers:=cheap_probe_A_fibers T S A B C e.2 parents pp.2.1 x y xA yA xd yn o member
 have originalTargetPart : partitionCheck (leaves T) [A,B,C]=true:=
  (partition_labels_congr (leaves S) (leaves T) _ (fun _=>pp.2.2.mem_iff.symm)).mp parents
 obtain ⟨t,ht,tl⟩:=checked_restrictions T [A,B,C] pp.1 originalTargetPart A (by simp)
 obtain ⟨s,hs,sl⟩:=checked_restrictions S [A,B,C] pp.2.1 parents A (by simp)
 have localProper : DepthOne.proper t s=true:= (DepthOne.proper_iff t s).mpr
  ⟨restricted_nodup T t A ht pp.1,restricted_nodup S s A hs pp.2.1,tl.trans sl.symm⟩
 have targetPartP : partitionCheck (leaves T) o.partition=true:=
  (partition_labels_congr (leaves S) (leaves T) _ (fun _=>pp.2.2.mem_iff.symm)).mp scope.2.1
 have sourceLocalPart:=local_partition S s A o.partition [A,B,C] hs scope.2.1 parents ref (by simp)
 have targetLocalPart:=local_partition T t A o.partition [A,B,C] ht targetPartP originalTargetPart ref (by simp)
 have sub : ∀K,K∈family A o.partition→K⊆A:=fun K hk=>(family_members_fresh K A o.partition).mp hk |>.2
 have sourceLocalEmb : pairwiseEmbeddings s (family A o.partition)=true:=
  (pairwise_transport S s A (family A o.partition) hs sub).mp
   ((pairwise_iff S _).mpr (List.Pairwise.filter _ ((pairwise_iff S _).mp scope.2.2.1)))
 have targetLocalEmb : pairwiseEmbeddings t (family A o.partition)=true:=
  (pairwise_transport T t A (family A o.partition) ht sub).mp
   (fiber_clade_embedding T S A o.partition e pp.1 scope.2.1 edge fibers)
 have blockGood : ∀K,K∈family A o.partition→restrictionAgrees t s K=true := by
  intro K kF
  have globalGood:=fiber_parent_good T S A D e.2 o.partition rfl fibers yesGood noGood K kF
  have sourceGood : restrictionAgrees T s K=true:=by
   rw [FreshResidual.materialized_restriction hs (fun z hz=>sub K kF hz)]
   exact globalGood
  apply ContactedHard2DP.restriction_good_swap
  rw [FreshResidual.materialized_restriction ht (fun z hz=>sub K kF hz)]
  exact ContactedHard2DP.restriction_good_swap sourceGood
 have localAF : agreement t s (family A o.partition)=true := by
  simp only [agreement,Bool.and_eq_true,List.all_eq_true]
  exact ⟨⟨⟨⟨targetLocalPart,sourceLocalPart⟩,blockGood⟩,targetLocalEmb⟩,sourceLocalEmb⟩
 have lengths:=(three_family_perm A B C o.partition (partition_parent_apart _ _ _ _ parents) ref
  (partition_nonempty_member _ _ scope.2.1)).length_eq
 have bpos:=checked_parent_family_positive _ [A,B,C] o.partition B parents scope.2.1 ref (by simp)
 have cpos:=checked_parent_family_positive _ [A,B,C] o.partition C parents scope.2.1 ref (by simp)
 simp only [List.length_append] at lengths
 have small : (family A o.partition).length-1≤1:=by have bound:=scope.2.2.2.1;omega
 cases pre : DepthOne.pretest01 t s with
 | refused=>
  have refused:=(DepthOne.refused_iff t s).mp pre
  exact False.elim (Bool.noConfusion (refused.symm.trans localProper))
 | rejected=>
  have lower:=DepthOne.rejected_lower_bound t s pre (family A o.partition) localAF
  omega
 | found choice=>
  cases choice with
  | some p=>
   refine ⟨DepthOne.forest s (some p),?_⟩
   simp only [BothBad.knownOne,ht,hs,pre]
  | none=>
   have valid:=(DepthOne.found_spec t s none pre).2.2.1
   have goodLocal : restrictionAgrees t s (leaves s)=true:=by
    have h:=valid
    simp only [DepthOne.forest,agreement,Bool.and_eq_true,List.all_cons,List.all_nil,Bool.and_true] at h
    exact h.1.1.2
   have masks : ∀z,(leaves s).contains z=A.contains z:=by
    intro z
    apply Bool.eq_iff_iff.mpr
    simpa only [List.contains_iff_mem] using sl.mem_iff
   rw [ContactedHard2DP.restriction_mask t s (leaves s) A masks,
    FreshResidual.materialized_restriction hs (fun _ hz=>hz)] at goodLocal
   have swapped:=ContactedHard2DP.restriction_good_swap goodLocal
   rw [FreshResidual.materialized_restriction ht (fun _ hz=>hz)] at swapped
   exact False.elim (Bool.noConfusion (badA.symm.trans swapped))
end ContactedHard2Survival

-- Author integration type/axiom reports; proof text above is unchanged apart from recorded import edits.
set_option pp.universes true
#check @ContactedHard2Survival.checked_parent_family_positive
#print axioms ContactedHard2Survival.checked_parent_family_positive
#check @ContactedHard2Survival.probe_source_refines
#print axioms ContactedHard2Survival.probe_source_refines
#check @ContactedHard2Survival.cheap_probe_knownOne
#print axioms ContactedHard2Survival.cheap_probe_knownOne
