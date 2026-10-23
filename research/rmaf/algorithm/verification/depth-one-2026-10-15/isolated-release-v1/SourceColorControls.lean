import ConsumerControls

namespace Universal233.DepthOne.SourceColorControls
open RMAF CoreProgram

theorem crossed_two_color_no_one_cut :
    (generate Controls.crossed (twoColor [0,1]) 1).outputs = [] := by decide

theorem crossed_two_color_two_cuts_exist :
    (generate Controls.crossed (twoColor [0,1]) 2).outputs.length = 2 := by decide

theorem crossed_whole_blocks_not_source_valid :
    partitionCheck (leaves Controls.crossed) [[0,1],[2,3]] = true ∧
    pairwiseEmbeddings Controls.crossed [[0,1],[2,3]] = false := by decide

end Universal233.DepthOne.SourceColorControls
