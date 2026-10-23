import OverlapControls
namespace Universal233.Hard2Overlap.Controls
open RMAF VertexGeometry Rule5Local.Pre
set_option maxRecDepth 10000
example : Hard2Overlap.select t6 [0,3] [1,4] [2,5]=some .disjoint := by decide
example : Hard2Overlap.select t6 [0,1] [2,5] [3,4]=some (.four .abc [false] [true]) := by decide
example : Hard2Overlap.select t7 [0,1] [2,5,6] [3,4]=some (.diagonal .abc [false] [true]) := by decide
example : Hard2Overlap.select t5 [4] [0,2] [1,3]=some (.pair .abc (.edge ([false],[false,false]))) := by decide
example : runHard2 commonT commonS firstCommon=some .disjoint := by decide
example : runHard2 commonT commonS firstCommon=some (.pair .acb (.vertex [false,false])) := by decide
example : ([[0,1],[2],[3]].filter (fun B=>restrictionAgrees t4 t4 B)).length=2 := by decide
end Universal233.Hard2Overlap.Controls
