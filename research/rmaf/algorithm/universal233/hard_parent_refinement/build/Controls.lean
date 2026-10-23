import Safety

namespace Universal233.HardParent
open RMAF CoreGraph Integration VertexGeometry CutRealization

/-- Actual original components, including the original root and all unary
vertices left after the cuts. The root-LCA fixture has singleton pendants. -/
theorem control_root_lca_actual_components :
    LiteralOriginalThree source4 [false,true] [true,true] :=
  (actual_hard2_named_safety (by decide) control_clean_agreement
    (p := [false]) (a := 0) (b := 1) (by rfl) control_root_lca_cuts).1

theorem control_root_lca_no_leafless : ∀ v, Valid source4 v →
    ∃ w x, LeafAt source4 w x ∧ ResidualWalk source4 [[false,true],[true,true]] v w :=
  control_root_lca_actual_components.no_leafless

theorem control_exact_refinement_consumer :
    VertexGeometry.Refines [[0,1],[2],[3]] (literalThree source4 [false,true] [true,true]) := by
  have h := (actual_hard2_named_safety (by decide) control_clean_agreement
    (p := [false]) (a := 0) (b := 1) (by rfl) control_root_lca_cuts).2.2
  rcases h with h | h | h
  · simp at h
  · simp at h
  · exact h

theorem control_above_lca_actual_components :
    LiteralOriginalThree source5 [false,false,true] [false,true,true] :=
  (actual_hard2_named_safety (by decide) control_upward_region_allowed
    (p := [false,false]) (a := 0) (b := 1) (by rfl) control_upward_region_cuts).1

theorem control_above_lca_no_leafless : ∀ v, Valid source5 v →
    ∃ w x, LeafAt source5 w x ∧ ResidualWalk source5 [[false,false,true],[false,true,true]] v w :=
  control_above_lca_actual_components.no_leafless

theorem control_above_lca_refinement_consumer :
    VertexGeometry.Refines [[0,1,4],[2],[3]]
      (literalThree source5 [false,false,true] [false,true,true]) := by
  have h := (actual_hard2_named_safety (by decide) control_upward_region_allowed
    (p := [false,false]) (a := 0) (b := 1) (by rfl) control_upward_region_cuts).2.2
  rcases h with h | h | h
  · simp at h
  · simp at h
  · exact h

theorem control_unordered_cherry_consumer :
    ∃ q r, pendantOriginal source4 1 0 = [q,r] ∧ LiteralOriginalThree source4 q r ∧
      partitionCheck (leaves source4) (literalThree source4 q r) = true ∧
      ([1] ∈ [[0,1],[2],[3]] ∨ [0] ∈ [[0,1],[2],[3]] ∨
        VertexGeometry.Refines [[0,1],[2],[3]] (literalThree source4 q r)) :=
  actual_hard2_unordered_safety (by decide) control_clean_agreement
    ⟨[false],Or.inr rfl⟩ (by decide)

theorem control_original_path_identification (w : RMAF.Vertex) :
    w ∈ minimalVertices [0,1] source4 ↔ PathAt w [false,false] [true,false] :=
  pair_minimal_path (S := source4) (a := 0) (b := 1)
    (u := [false,false]) (v := [true,false]) (by decide) rfl rfl w

theorem control_duplicate_label_input_rejected :
    ¬(leaves (Tree.node (Tree.node (.leaf 0) (.leaf 2)) (.node (.leaf 1) (.leaf 2)))).Nodup := by decide

-- Private generated declarations must also appear in the module-origin audit.
private theorem internal_control : (pendantOriginal source4 0 1).length = 2 := by decide

theorem control_private_declaration_consumer : (pendantOriginal source4 0 1).length = 2 := internal_control
end Universal233.HardParent
