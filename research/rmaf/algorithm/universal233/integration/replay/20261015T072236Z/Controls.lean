import CutRecords

namespace Universal233.Integration.Controls
open RMAF CoreGraph CoreProgram

def twoLabels : Tree := .node (.leaf 0) (.leaf 2)
def parity (x : Nat) : Nat := x % 2

theorem clean_partition_check : RMAF.partitionCheck (RMAF.leaves twoLabels) [[0],[2]] = true := by decide

theorem clean_embedding_check : RMAF.pairwiseEmbeddings twoLabels [[0],[2]] = true := by decide

noncomputable def cleanPartition : SourcePartition twoLabels :=
  checkedSourcePartition twoLabels [[0],[2]] clean_partition_check clean_embedding_check

theorem clean_distinct_owners : cleanPartition.owner [false] ≠ cleanPartition.owner [true] := by
  intro he
  have hf := (checkedSourcePartition_owner twoLabels [[0],[2]] clean_partition_check clean_embedding_check
    [false] [true] 0 2 rfl rfl).1 he
  simp at hf

theorem whole_hull_walk : Walk twoLabels (fun v => v ∈ RMAF.minimalVertices [0,2] twoLabels)
    [false] [true] := minimalVertices_connected [0,2] twoLabels [false] [true] (by decide) (by decide)

theorem exact_original_payload_normalization : normalize (fromTree parity [] twoLabels) =
    .leaf ⟨[],[0,2],0⟩ := by decide

def expandedTree : Tree := .node (.node (.leaf 0) (.leaf 1)) (.leaf 2)
def expandedErasure : LeafErasure expandedTree (.node (.leaf 1) (.leaf 2)) :=
  .left (.leaf 2) (.rootLeft 0 (.leaf 1))

theorem suppression_expands_edge_to_path : erasureEmbedding expandedErasure [] = [] ∧
    erasureEmbedding expandedErasure [false] = [false,true] := by decide

theorem suppressed_edge_is_not_original_edge :
    ¬Adj expandedTree (erasureEmbedding expandedErasure []) (erasureEmbedding expandedErasure [false]) := by
  intro h
  rcases h.2.2 with ⟨s,hs⟩ | ⟨s,hs⟩
  · have hl := congrArg List.length hs
    simp [expandedErasure,erasureEmbedding] at hl
  · have hl := congrArg List.length hs
    simp [expandedErasure,erasureEmbedding] at hl

theorem suppression_original_path :
    VertexGeometry.PathAt [false] (erasureEmbedding expandedErasure [])
      (erasureEmbedding expandedErasure [false]) := by
  exact VertexGeometry.PathAt.rightLeg false (VertexGeometry.PathAt.endpointL [] [true])

theorem clean_erase_source_partition :
    ∃ Q : SourcePartition (.node (.leaf 1) (.leaf 2)), Monochromatic Q id := by
  have hp : RMAF.partitionCheck (RMAF.leaves expandedTree) [[0],[1],[2]] = true := by decide
  have he : RMAF.pairwiseEmbeddings expandedTree [[0],[1],[2]] = true := by decide
  let P := checkedSourcePartition expandedTree [[0],[1],[2]] hp he
  refine ⟨erasePartition expandedErasure P,erasePartition_monochromatic expandedErasure P id ?_⟩
  apply checkedSourcePartition_monochromatic expandedTree [[0],[1],[2]] hp he id
  intro b hb x y hx hy
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with rfl | rfl | rfl <;> simp_all

end Universal233.Integration.Controls
