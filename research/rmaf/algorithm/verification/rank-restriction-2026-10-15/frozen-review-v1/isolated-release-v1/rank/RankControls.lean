import RationalMass

namespace Universal233.RankDichotomy.Controls
open RMAF CoreProgram SourceCoverage VertexGeometry

def quartet : Tree := .node (.node (.leaf 0) (.leaf 1)) (.node (.leaf 2) (.leaf 3))
def contiguous (x : Nat) : Nat := if x < 2 then 0 else 1
def crossed (x : Nat) : Nat := x % 2

theorem contiguous_output :
    (generate quartet contiguous 3).outputs.length = 1 ∧
    CoreProgram.Controls.costs (generate quartet contiguous 3) = [1] ∧
    CoreProgram.Controls.parts (generate quartet contiguous 3) = [[[0,1],[2,3]]] := by decide

theorem contiguous_source_valid : partitionCheck (leaves quartet) [[0,1],[2,3]] = true ∧
    pairwiseEmbeddings quartet [[0,1],[2,3]] = true := by decide

theorem crossed_outputs : CoreProgram.Controls.costs (generate quartet crossed 3) = [2,2] ∧
    CoreProgram.Controls.parts (generate quartet crossed 3) =
      [[[0],[1,3],[2]],[[0,2],[1],[3]]] := by decide

theorem crossed_label_only_false : partitionCheck (leaves quartet) [[0,2],[1,3]] = true ∧
    pairwiseEmbeddings quartet [[0,2],[1,3]] = false := by decide

theorem all_distinct : (generate quartet id 3).outputs.length = 1 ∧
    CoreProgram.Controls.costs (generate quartet id 3) = [3] := by decide

theorem repeated_refusal :
    (generate (.node (.leaf 0) (.leaf 0)) id 3).outputs = [] ∧
    (generate (.node (.leaf 0) (.leaf 0)) id 3).refusals = ["duplicate original label"] := by decide

theorem q0_pruning : (generate quartet contiguous 0).outputs = [] ∧
    (generate quartet contiguous 0).pruned = 1 ∧
    (generate quartet crossed 0).outputs = [] ∧
    (generate quartet crossed 0).pruned = 2 := by decide

theorem refinement_direction :
    RefinesBlocks [[0],[1],[2],[3]] [[0,1],[2,3]] ∧
    ¬RefinesBlocks [[0,1],[2,3]] [[0],[1],[2],[3]] := by
  simp [RefinesBlocks]

theorem crossed_rawmass : rawQMass 3 (generate quartet crossed 3).outputs = (2/9 : Rat) := by
  change (3 : Rat)^(-2 : Int) + ((3 : Rat)^(-2 : Int) + 0) = _
  rw [Rat.zpow_neg]
  change ((3 : Rat)^(2 : Nat))⁻¹ + (((3 : Rat)^(2 : Nat))⁻¹ + 0) = _
  with_unfolding_all decide
theorem crossed_sharp_mass : rawQMass 3 (generate quartet crossed 3).outputs = 2*(3 : Rat)^(-2 : Int) := by
  rw [crossed_rawmass, Rat.zpow_neg]
  change (2/9 : Rat) = 2*((3 : Rat)^(2 : Nat))⁻¹
  with_unfolding_all decide

end Universal233.RankDichotomy.Controls
