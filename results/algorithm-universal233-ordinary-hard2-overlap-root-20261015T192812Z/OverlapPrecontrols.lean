import HardPaid
import VertexPair
import HardForest
import Selector
namespace Universal233.Hard2Overlap.Controls
open RMAF VertexGeometry
set_option maxRecDepth 10000
def t4 : Tree := .node (.node (.leaf 0) (.leaf 1)) (.node (.leaf 2) (.leaf 3))
def t5 : Tree := .node t4 (.leaf 4)
def t6 : Tree := .node (.node (.leaf 0) (.node (.leaf 1) (.leaf 2))) (.node (.leaf 3) (.node (.leaf 4) (.leaf 5)))
def t7 : Tree := .node (.node (.node (.leaf 0) (.leaf 6)) (.node (.leaf 1) (.leaf 2))) (.node (.leaf 3) (.node (.leaf 4) (.leaf 5)))
theorem disjoint_fixture : pairwiseEmbeddings t4 [[0,1],[2],[3]]=true := by decide
theorem clique_partition : partitionCheck (leaves t6) [[0,3],[1,4],[2,5]]=true := by decide
theorem clique_literal : []∈minimalVertices [0,3] t6 ∧ []∈minimalVertices [1,4] t6 ∧ []∈minimalVertices [2,5] t6 := by decide
theorem chain_partition : partitionCheck (leaves t6) [[0,1],[2,5],[3,4]]=true := by decide
theorem chain_literal : [false]∈minimalVertices [0,1] t6 ∧ [false]∈minimalVertices [2,5] t6 ∧ [true]∈minimalVertices [2,5] t6 ∧ [true]∈minimalVertices [3,4] t6 := by decide
theorem chain_ends_disjoint : disjointVertices (minimalVertices [0,1] t6) (minimalVertices [3,4] t6)=true := by decide
theorem diagonal_count : (jointColors [2,5] t6 [false] [true]).length=2 := by decide
theorem four_partition : partitionCheck (leaves t7) [[0,1],[2,5,6],[3,4]]=true := by decide
theorem four_literal : [false]∈minimalVertices [0,1] t7 ∧ [false]∈minimalVertices [2,5,6] t7 ∧ [true]∈minimalVertices [2,5,6] t7 ∧ [true]∈minimalVertices [3,4] t7 := by decide
theorem four_count : (jointColors [2,5,6] t7 [false] [true]).length=3 := by decide
theorem isolated_partition : partitionCheck (leaves t5) [[0,2],[1,3],[4]]=true := by decide
theorem isolated_pair : PairGeometry.properInput t5 [0,2] [1,3]=true ∧ (PairGeometry.choose t5 [0,2] [1,3]).isSome=true := by decide
theorem isolated_other : pairwiseEmbeddings t5 [[0,2],[4]]=true ∧ pairwiseEmbeddings t5 [[1,3],[4]]=true := by decide
end Universal233.Hard2Overlap.Controls
