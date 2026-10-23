import CheapProbeFibers
open RMAF VertexGeometry ForestState ForestGroups RestrictionBridge OutputState Universal233 Universal233.CoreProgram
namespace ContactedHard2Survival

theorem fiber_clade_embedding (T S : Tree) (A : List Nat) (P : List (List Nat))
 (e : RMAF.Vertex×RMAF.Vertex) (nd : (leaves T).Nodup)
 (part : partitionCheck (leaves S) P=true) (edge : e∈PairGeometry.edges T)
 (fibers : ∀K,K∈family A P→∃inside : Bool,∀z,z∈K ↔ z∈PairGeometry.sideLabels A T e.2 inside) :
 pairwiseEmbeddings T (family A P)=true := by
 obtain ⟨U,subtree⟩:=edge_child_subtree T e edge
 have labels:=descendants_child_clade T U e.2 nd subtree
 have familyND : (family A P).Nodup:=List.Pairwise.filter _ (checked_family_nodup _ _ part)
 have cross : ∀K,K∈family A P→∀J,J∈family A P→K≠J→Clear (minimalVertices K T) (minimalVertices J T) := by
  intro K kF J jF diff
  obtain ⟨ki,klabels⟩:=fibers K kF
  obtain ⟨ji,jlabels⟩:=fibers J jF
  have kp:=(family_members_fresh K A P).mp kF
  have jp:=(family_members_fresh J A P).mp jF
  have sameImpossible : ki=ji→False := by
   intro eq
   subst ji
   obtain ⟨z,zK⟩:=List.exists_mem_of_ne_nil K (partition_nonempty_member _ _ part K kp.1)
   exact diff (group_unique _ _ part K J kp.1 jp.1 z zK ((jlabels z).mpr ((klabels z).mp zK)))
  have trueFalse : ∀X Y : List Nat,(∀z,z∈X→z∈PairGeometry.sideLabels A T e.2 true)→
    (∀z,z∈Y→z∈PairGeometry.sideLabels A T e.2 false)→Clear (minimalVertices X T) (minimalVertices Y T) := by
   intro X Y inside outside v vx vy
   have is : ∀z,z∈X→z∈leaves U:=by
    intro z hz
    exact (labels z).mp (by simpa using (List.mem_filter.mp (inside z hz)).2)
   have out : ∀z,z∈leaves U→z∉Y:=by
    intro z hz hy
    have no : z∉PairGeometry.descendants T e.2:=by simpa using (List.mem_filter.mp (outside z hy)).2
    exact no ((labels z).mpr hz)
   exact ContactedClade.clade_span_disjoint subtree nd is out v vx (IndependentGeometry.minimal_in_span _ _ v vy)
  cases ki <;>cases ji
  · exact False.elim (sameImpossible rfl)
  · exact (clear_symm _ _).mpr (trueFalse J K (fun z hz=>(jlabels z).mp hz) (fun z hz=>(klabels z).mp hz))
  · exact trueFalse K J (fun z hz=>(klabels z).mp hz) (fun z hz=>(jlabels z).mp hz)
  · exact False.elim (sameImpossible rfl)
 apply (pairwise_iff T (family A P)).mpr
 exact List.Pairwise.imp_of_mem (fun {K J} kF jF diff=>cross K kF J jF diff) familyND

theorem fiber_parent_good (T S : Tree) (A D : List Nat) (p : RMAF.Vertex) (P : List (List Nat))
 (hD : D=PairGeometry.descendants T p)
 (fibers : ∀K,K∈family A P→∃inside : Bool,∀z,z∈K ↔ z∈PairGeometry.sideLabels A T p inside)
 (yesGood : restrictionAgrees S T (BinaryCheap.ay A D)=true)
 (noGood : restrictionAgrees S T (BinaryCheap.an A D)=true) :
 ∀K,K∈family A P→restrictionAgrees T S K=true := by
 intro K kF
 obtain ⟨inside,labels⟩:=fibers K kF
 have masks : ∀z,K.contains z=(PairGeometry.sideLabels A T p inside).contains z := by
  intro z
  apply Bool.eq_iff_iff.mpr
  simpa only [List.contains_iff_mem] using labels z
 have rawGood : restrictionAgrees S T (PairGeometry.sideLabels A T p inside)=true := by
  subst D
  cases inside
  · exact noGood
  · exact yesGood
 apply ContactedHard2DP.restriction_good_swap
 rw [ContactedHard2DP.restriction_mask S T K _ masks]
 exact rawGood
end ContactedHard2Survival

-- Author integration type/axiom reports; proof text above is unchanged apart from recorded import edits.
set_option pp.universes true
#check @ContactedHard2Survival.fiber_clade_embedding
#print axioms ContactedHard2Survival.fiber_clade_embedding
#check @ContactedHard2Survival.fiber_parent_good
#print axioms ContactedHard2Survival.fiber_parent_good
