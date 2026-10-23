-- Deliberately false controls: each declaration MUST fail kernel construction.
import Controls13
open RMAF Universal233 OwnHigh
theorem corrupt_wrong_partition : CherryBranching.pendantPartition S1 0 1 = [[0],[1],[2]] := by decide
theorem corrupt_omit_a : [1] ∈ [[0],[1,2]] ∨ refinesB [[0],[1,2]] [[2],[0,1]] = true := by decide
theorem corrupt_omit_b : [0] ∈ [[1],[0,2]] ∨ refinesB [[1],[0,2]] [[2],[0,1]] = true := by decide
theorem corrupt_swapped_source : CherryBranching.pendantPartition T1 0 1 = [[2],[0,1]] := by decide
theorem corrupt_equal_distinct : (0 : Nat) ≠ 0 := by decide
theorem corrupt_improper_accepted : DepthOne.proper (.node (.leaf 0) (.leaf 1)) (.node (.leaf 0) (.leaf 2)) = true := by decide
