import FreshActualReadoutsV2
open RMAF RestrictionBridge ForestState ForestGroups OutputState FreshOutputReadouts
theorem clean_wrong_target_Q_clear : pairwiseEmbeddings (.node (.node (.leaf 0) (.leaf 2)) (.node (.leaf 1) (.leaf 3))) [[0,1],[2,3]] = false := by decide

theorem clean_omitted_source_Q_original : agreement (.node (.node (.leaf 0) (.leaf 1)) (.node (.leaf 2) (.leaf 3))) (.node (.node (.leaf 0) (.leaf 2)) (.node (.leaf 1) (.leaf 3))) [[0,1],[2,3]] = false := by decide

theorem clean_dropped_entry_count : (sourceForest (.node (.node (.leaf 0) (.leaf 1)) (.node (.leaf 2) (.leaf 3))) [[0,1],[],[2,3]]).length = 2 := by decide

theorem clean_canonical_order_assumption : sourceForest (.node (.node (.leaf 0) (.leaf 1)) (.node (.leaf 2) (.leaf 3))) [[3,2],[1,0]] = [.node (.leaf 2) (.leaf 3),.node (.leaf 0) (.leaf 1)] := by decide

theorem clean_fabricated_A_zero : additionalCost groupAs fa = 1 := by decide

theorem clean_forced_B_internal_clearance : pairwiseEmbeddings groupT [[3,5],[4,6]] = false := by decide

theorem clean_omitted_B_piece : groupBs.length = 2 := by decide

theorem clean_free_whole_B_substitution : additionalCost groupBs fbCheap = 1 := by decide
