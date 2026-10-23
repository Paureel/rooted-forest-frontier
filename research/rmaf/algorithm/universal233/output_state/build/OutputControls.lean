import OutputDefs
namespace OutputState.Controls
open RMAF ForestState OutputState
-- These compact quartet shapes are declared development contacts with the
-- completed restriction/group controls; no independent-verification label.
def ordinary : Tree := .node (.node (.leaf 0) (.leaf 1)) (.node (.leaf 2) (.leaf 3))
def crossed : Tree := .node (.node (.leaf 0) (.leaf 2)) (.node (.leaf 1) (.leaf 3))
def Q : List (List Nat) := [[0,2],[1,3]]
def F : List (List Nat) := [[0],[2],[1],[3]]
theorem source_valid_target_overlap : partitionCheck (leaves crossed) Q = true ∧
    pairwiseEmbeddings crossed Q = true ∧ pairwiseEmbeddings ordinary Q = false := by decide
theorem refining_valid : agreement ordinary crossed F = true ∧
    agrees (some ordinary) (sourceForest crossed Q) F = true := by decide
theorem exact_components : sourceForest crossed Q = [.node (.leaf 0) (.leaf 2),.node (.leaf 1) (.leaf 3)] ∧
    (sourceForest crossed Q).map leaves = Q ∧ (sourceForest crossed Q).length = Q.length := by decide
theorem source_overlap_reverse_fire : partitionCheck (leaves ordinary) Q = true ∧
    pairwiseEmbeddings ordinary Q = false ∧
    agrees (some crossed) (sourceForest ordinary Q) Q = true ∧
    agreement crossed ordinary Q = false := by decide
theorem permuted : agrees (some ordinary) (sourceForest crossed [[3,1],[2,0]]) [[3],[0],[1],[2]] = true ∧
    additionalCost (sourceForest crossed [[3,1],[2,0]]) [[3],[0],[1],[2]] = 2 := by decide
theorem singleton_boundary : sourceForest (.leaf 19) [[19]] = [.leaf 19] ∧
    agrees (some (.leaf 19)) (sourceForest (.leaf 19) [[19]]) [[19]] = true := by decide
theorem full_boundary : sourceForest ordinary [[3,2,1,0]] = [ordinary] ∧
    agrees (some ordinary) (sourceForest ordinary [[3,2,1,0]]) [[3,2,1,0]] = true := by decide
theorem zeros_boundary : sourceForest ordinary [] = [] ∧ agrees none [] [] = true := by decide
end OutputState.Controls
