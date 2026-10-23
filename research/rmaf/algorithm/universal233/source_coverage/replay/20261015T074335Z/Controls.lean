import OutputBudget

namespace Universal233.SourceCoverage.Controls
open RMAF CoreProgram CoreGraph Integration VertexGeometry

abbrev quartet := CoreProgram.Controls.crossed
abbrev parity := CoreProgram.Controls.parity

theorem mixed_cherry_paid :
    CoreProgram.Controls.costs (generate quartet parity 2) = [2,2] := by decide

theorem mixed_cherry_original_refinement :
    ∃ o, o ∈ (generate quartet parity 2).outputs ∧
      RefinesBlocks [[0,2],[1],[3]] o.partition ∧ o.sourceCuts.length ≤ 2 := by
  apply generate_partition_coverage_paid quartet [[0,2],[1],[3]] parity
    (by decide) (by decide) (by decide) _ 2 (by decide)
  intro b hb x y hx hy
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with rfl | rfl | rfl <;> simp_all [parity,CoreProgram.Controls.parity] <;> omega

theorem unique_singleton :
    CoreProgram.Controls.costs (generate CoreProgram.Controls.cherry3 id 2) = [2] ∧
    (generate CoreProgram.Controls.cherry3 id 2).childAttempts = 2 := by decide

def thirdParentColor (x : Nat) := if x = 1 then 1 else 0

theorem third_parent_homogeneous_contraction :
    CoreProgram.Controls.parts (generate CoreProgram.Controls.cherry3 thirdParentColor 2) =
      [[[0,2],[1]]] := by decide

theorem third_parent_preserves_original_singletons :
    ∃ o, o ∈ (generate CoreProgram.Controls.cherry3 thirdParentColor 2).outputs ∧
      RefinesBlocks [[0],[1],[2]] o.partition ∧ o.sourceCuts.length ≤ 2 := by
  apply generate_partition_coverage_paid CoreProgram.Controls.cherry3 [[0],[1],[2]] thirdParentColor
    (by decide) (by decide) (by decide) _ 2 (by decide)
  intro b hb x y hx hy
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with rfl | rfl | rfl <;> simp_all

theorem budget_zero_pruned :
    (generate CoreProgram.Controls.cherry3 id 0).outputs = [] ∧
    (generate CoreProgram.Controls.cherry3 id 0).visited = 1 ∧
    (generate CoreProgram.Controls.cherry3 id 0).childAttempts = 1 ∧
    (generate CoreProgram.Controls.cherry3 id 0).pruned = 1 := by decide

theorem exact_budget_prune_counted :
    (generate quartet parity 1).outputs = [] ∧
    (generate quartet parity 1).visited = 3 ∧
    (generate quartet parity 1).childAttempts = 4 ∧
    (generate quartet parity 1).pruned = 2 := by decide

theorem exact_budget_finishes :
    (generate quartet parity 2).outputs.length = 2 ∧
    (generate quartet parity 2).visited = 5 ∧
    (generate quartet parity 2).childAttempts = 4 ∧
    (generate quartet parity 2).pruned = 0 := by decide

theorem duplicate_input_refused :
    (generate (.node (.leaf 4) (.leaf 4)) id 9).refusals = ["duplicate original label"] ∧
    (generate (.node (.leaf 4) (.leaf 4)) id 9).outputs = [] := by decide

end Universal233.SourceCoverage.Controls
