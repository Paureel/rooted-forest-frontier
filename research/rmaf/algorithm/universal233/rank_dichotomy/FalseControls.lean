import Controls
open RMAF Universal233.CoreProgram Universal233.SourceCoverage
open Universal233.RankDichotomy.Controls

theorem false_label_only_embedding : pairwiseEmbeddings quartet [[0,2],[1,3]] = true := by decide
theorem false_refinement_direction : RefinesBlocks [[0,1],[2,3]] [[0],[1],[2],[3]] := by
  simp [RefinesBlocks]
theorem false_rawmass : rawQMass 3 (generate quartet crossed 3).outputs ≤ (3 : Rat)^(-2 : Int) := by
  rw [crossed_rawmass, Rat.zpow_neg]
  change (2/9 : Rat) ≤ ((3 : Rat)^(2 : Nat))⁻¹
  with_unfolding_all decide
