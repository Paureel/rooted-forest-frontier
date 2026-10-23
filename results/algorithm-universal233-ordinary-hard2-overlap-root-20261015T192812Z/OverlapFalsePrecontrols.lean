import OverlapPrecontrols
namespace Universal233.Hard2Overlap.Controls
open RMAF VertexGeometry
set_option maxRecDepth 10000
example : pairwiseEmbeddings t6 [[0,3],[1,4],[2,5]]=true := by decide
example : (jointColors [2,5] t6 [false] [true]).length=1 := by decide
example : (jointColors [2,5,6] t7 [false] [true]).length=2 := by decide
example : (PairGeometry.choose t5 [0,2] [1,3]).isSome=false := by decide
end Universal233.Hard2Overlap.Controls
