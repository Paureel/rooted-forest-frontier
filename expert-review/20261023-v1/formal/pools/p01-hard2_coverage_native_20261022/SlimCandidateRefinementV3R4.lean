/- Reused own frozen proof body; slim import slice, permanently CONTACTED. -/
/- Contacted partial repair: the candidate preserves literal pendant refinement. -/
import SlimRepairCandidateTargetV3R4
open RMAF ForestState Universal233 Universal233.HardParent Universal233.CherryBranching
open IndependentGeometry IndependentOneExchange ContactedClade
namespace ContactedRepair

theorem expand_shrink_labels {a b z : Nat} {B : List Nat} (fresh : z∉B) {x : Nat}
 (hx : x∈expandBlock a b z (shrinkBlock a b z B)) :
 (x∈B ∧ x≠b) ∨ (a∈B ∧ (x=a∨x=b)) := by
 rcases (expand_membership _ a b z x).1 hx with ⟨old,xz⟩|⟨old,endpoint⟩
 · obtain ⟨y,hy,eq⟩ := List.mem_map.1 old
   have p := List.mem_filter.1 hy
   by_cases ya : y=a
   · have zx : z=x := by simpa [ya] using eq
     exact False.elim (xz zx.symm)
   · have yx : y=x := by simpa [ya] using eq
     have yb : y≠b := by simpa using p.2
     exact Or.inl ⟨yx ▸ p.1,fun xb=>yb (yx.trans xb)⟩
 · obtain ⟨y,hy,eq⟩ := List.mem_map.1 old
   have p := List.mem_filter.1 hy
   by_cases ya : y=a
   · exact Or.inr ⟨ya ▸ p.1,endpoint⟩
   · have yz : y=z := by simpa [ya] using eq
     exact False.elim (fresh (yz ▸ p.1))

theorem merge_refines_binary (a b z : Nat) (X Y : List Nat) (G : List (List Nat))
 (fresh : ∀B∈G,z∉B) (noA : a∉X) (aY : a∈Y) (bY : b∈Y)
 (ref : VertexGeometry.Refines G [X,Y]) :
 VertexGeometry.Refines (mergeCommon a b z G) [X,Y] := by
 intro A ha
 obtain ⟨C,hC,rfl⟩ := List.mem_map.1 ha
 have old := (List.mem_filter.1 hC).1
 obtain ⟨B,hB,eq⟩ := List.mem_map.1 old
 subst C
 obtain ⟨D,hD,sub⟩ := ref B hB
 simp only [List.mem_cons,List.not_mem_nil,or_false] at hD
 rcases hD with left|right
 · subst D
   refine ⟨X,by simp,?_⟩
   intro x hx
   rcases expand_shrink_labels (fresh B hB) hx with ⟨xb,_⟩|⟨ab,_⟩
   · exact sub x xb
   · exact False.elim (noA (sub a ab))
 · subst D
   refine ⟨Y,by simp,?_⟩
   intro x hx
   rcases expand_shrink_labels (fresh B hB) hx with ⟨xb,_⟩|⟨_,xa|xb⟩
   · exact sub x xb
   · exact xa ▸ aY
   · exact xb ▸ bY

theorem candidate_refines {T S U : Tree} {q p : Vertex} {a b z : Nat}
 (proper : DepthOne.proper T S=true) (ch : CoreGraph.CherryAt T q a b)
 (one : cuts S a b=[p]) (sub : CoreGraph.subtree S p=some U)
 {F : List (List Nat)} (hF : agreement T S F=true) (fresh : z∉leaves T) :
 VertexGeometry.Refines (repairCandidate a b z (leaves U) F) (pendantPartition S a b) := by
 have valid := original_clade_split_agreement T S U p F proper sub hF
 have part := valid
 simp only [agreement,Bool.and_eq_true] at part
 have fblocks : ∀B∈splitForest (leaves U) F,z∉B := fun B hB=>block_fresh fresh part.1.1.1.1 hB
 have cut : p∈cuts S a b := by simp [one]
 have outside := pendant_subtree_absent_endpoints cut sub
 have perm := (IndependentReconstruction.proper_parts proper).2.2
 have aS := perm.mem_iff.1 (subtree_leaves_own ch a (by simp [leaves]))
 have bS := perm.mem_iff.1 (subtree_leaves_own ch b (by simp [leaves]))
 let Y := (leaves S).filter (fun x=>!(leaves U).contains x)
 have aY : a∈Y := List.mem_filter.2 ⟨aS,by simpa using outside.1⟩
 have bY : b∈Y := List.mem_filter.2 ⟨bS,by simpa using outside.2⟩
 have before := (original_clade_split_full proper sub hF).2.2
 rw [pendant_partition_one one sub]
 by_cases hb : [b]∈splitForest (leaves U) F
 · simp only [repairCandidate,hb,ite_true]
   exact merge_refines_binary a b z _ Y _ fblocks outside.1 aY bY before
 · simp only [repairCandidate,hb,ite_false]
   exact merge_refines_binary b a z _ Y _ fblocks outside.2 bY aY before

/- Remaining original-source geometry only. This Prop is unproved. -/
def CandidateSourceGeometry : Prop := ∀T S U q p a b z F,
 DepthOne.proper T S=true→CoreGraph.CherryAt T q a b→cuts S a b=[p]→
 CoreGraph.subtree S p=some U→agreement T S F=true→
 ¬VertexGeometry.Refines F (pendantPartition S a b)→z∉leaves T→
 (repairCandidate a b z (leaves U) F).all (restrictionAgrees T S)=true ∧
 pairwiseEmbeddings S (repairCandidate a b z (leaves U) F)=true
end ContactedRepair

-- Author integration type/axiom reports; proof text above is unchanged apart from recorded import edits.
set_option pp.universes true
#check @ContactedRepair.expand_shrink_labels
#print axioms ContactedRepair.expand_shrink_labels
#check @ContactedRepair.merge_refines_binary
#print axioms ContactedRepair.merge_refines_binary
#check @ContactedRepair.candidate_refines
#print axioms ContactedRepair.candidate_refines
