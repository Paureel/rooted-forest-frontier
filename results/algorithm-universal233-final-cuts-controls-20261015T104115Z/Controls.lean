import RecoveryProgram

namespace Universal233.FinalCutRecovery.Controls
open RMAF CoreProgram

def quartet : Tree := .node (.node (.leaf 41) (.leaf 7)) (.node (.leaf 99) (.leaf 12))
def caterpillar : Tree := .node (.leaf 91) (.node (.leaf 7) (.node (.leaf 55) (.leaf 3)))

theorem whole_cost_zero : recover quartet [[12,41,99,7]] =
    some ⟨[[41,7,99,12]],[]⟩ := by decide

theorem arbitrary_labels_permuted_blocks : recover quartet [[12,99],[7,41]] =
    some ⟨[[41,7],[99,12]],[[false]]⟩ := by decide

theorem suppressed_path_original_cuts : recover caterpillar [[3,55],[91],[7]] =
    some ⟨[[7],[91],[55,3]],[[true,false],[false]]⟩ := by decide

theorem singleton_cost : ((recover quartet [[12],[7],[99],[41]]).map
    (fun o => o.sourceCuts.length)) = some 3 := by decide

theorem root_cut_rejected :
    (attempt (fun _ _ _ => ({} : Receipt)) (fromTree id [] quartet) [] []
      ⟨[],[41],41⟩).refusals = ["attempt to cut original root"] := by decide

theorem overlapping_blocks_rejected : recover quartet [[41,7],[7,99,12]] = none := by decide

theorem overlapping_embeddings_rejected :
    partitionCheck (leaves quartet) [[41,99],[7,12]] = true ∧
    recover quartet [[41,99],[7,12]] = none := by decide

theorem absent_label_rejected : recover quartet [[41,7],[99,77]] = none := by decide

theorem empty_block_rejected : recover quartet [[],[41,7,99,12]] = none := by decide

theorem repeated_source_rejected :
    recover (.node (.leaf 7) (.leaf 7)) [[7]] = none := by decide

theorem false_cut_list_caught :
    recover caterpillar [[3,55],[91],[7]] ≠
      some ⟨[[7],[91],[55,3]],[[true],[false]]⟩ := by decide

end Universal233.FinalCutRecovery.Controls
