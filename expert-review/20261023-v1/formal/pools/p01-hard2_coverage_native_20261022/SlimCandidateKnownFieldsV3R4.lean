/- Reused own frozen proof body; slim import slice, permanently CONTACTED. -/
/- Contacted partial repair: all established fields, with two source checks unsupplied. -/
import SlimCandidateRefinementV3R4
open RMAF ForestState Universal233 Universal233.HardParent Universal233.CherryBranching
open IndependentGeometry IndependentOneExchange ContactedClade
namespace ContactedRepair

theorem partition_other_labels {T S : Tree} {H : List (List Nat)}
 (proper : DepthOne.proper T S=true) (part : partitionCheck (leaves T) H=true) :
 partitionCheck (leaves S) H=true := by
 obtain ⟨nt,ns,perm⟩ := IndependentReconstruction.proper_parts proper
 have flat := IndependentCommon.flatten_from_partition _ H nt part
 have check := part
 simp only [partitionCheck,Bool.and_eq_true] at check
 have nonempty : ∀B∈H,B≠[] := by
  intro B hb empty
  have ok := List.all_eq_true.1 check.1.1 B hb
  simp [empty] at ok
 exact IndependentCommon.partition_from_flatten _ H ns nonempty (flat.trans perm)

theorem candidate_known_fields {T S U : Tree} {q p : Vertex} {a b z : Nat}
 (proper : DepthOne.proper T S=true) (ch : CoreGraph.CherryAt T q a b)
 (one : cuts S a b=[p]) (sub : CoreGraph.subtree S p=some U)
 {F : List (List Nat)} (hF : agreement T S F=true)
 (no : ¬VertexGeometry.Refines F (pendantPartition S a b)) (fresh : z∉leaves T) :
 agreement T T (repairCandidate a b z (leaves U) F)=true ∧
 partitionCheck (leaves S) (repairCandidate a b z (leaves U) F)=true ∧
 VertexGeometry.Refines (repairCandidate a b z (leaves U) F) (pendantPartition S a b) ∧
 (repairCandidate a b z (leaves U) F).length+1≤(splitForest (leaves U) F).length ∧
 (repairCandidate a b z (leaves U) F).length≤F.length := by
 have half := candidate_target_half proper ch one sub hF no fresh
 have parts := half.1
 simp only [agreement,Bool.and_eq_true] at parts
 exact ⟨half.1,partition_other_labels proper parts.1.1.1.1,
  candidate_refines proper ch one sub hF fresh,half.2⟩
end ContactedRepair

-- Author integration type/axiom reports; proof text above is unchanged apart from recorded import edits.
set_option pp.universes true
#check @ContactedRepair.partition_other_labels
#print axioms ContactedRepair.partition_other_labels
#check @ContactedRepair.candidate_known_fields
#print axioms ContactedRepair.candidate_known_fields
