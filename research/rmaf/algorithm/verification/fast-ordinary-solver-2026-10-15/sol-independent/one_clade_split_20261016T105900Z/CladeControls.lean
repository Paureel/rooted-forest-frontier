/- Fixed original-vertex controls for the contacted clade-split proof. -/
import CladeSplitAgreement
open RMAF ForestState Universal233 Universal233.HardParent Universal233.CherryBranching
open IndependentGeometry IndependentOneExchange
namespace ContactedClade

def balanced : Tree := .node (.node (.leaf 0) (.leaf 1)) (.node (.leaf 2) (.leaf 3))
def repeated : Tree := .node (.node (.leaf 0) (.leaf 1))
 (.node (.node (.leaf 0) (.leaf 2)) (.leaf 3))

theorem balanced_good_split :
 CoreGraph.subtree balanced [false]=some (.node (.leaf 0) (.leaf 1)) ∧
 agreement balanced balanced [[0,1,2,3]]=true ∧
 splitForest [0,1] [[0,1,2,3]]=[[0,1],[2,3]] ∧
 agreement balanced balanced (splitForest [0,1] [[0,1,2,3]])=true := by decide

theorem nonclade_shape_count_insufficient :
 partitionCheck (leaves balanced) (splitForest [0,2] [[0,1,2,3]])=true ∧
 (splitForest [0,2] [[0,1,2,3]]).all (restrictionAgrees balanced balanced)=true ∧
 (splitForest [0,2] [[0,1,2,3]]).length≤2 ∧
 ([] : Vertex)∈minimalVertices [0,2] balanced ∧
 ([] : Vertex)∈minimalVertices [1,3] balanced ∧
 agreement balanced balanced (splitForest [0,2] [[0,1,2,3]])=false := by decide

theorem proper_nodup_needed :
 CoreGraph.subtree repeated [false]=some (.node (.leaf 0) (.leaf 1)) ∧
 agreement repeated repeated [[0,1,2,3]]=true ∧
 DepthOne.proper repeated repeated=false ∧
 ([true] : Vertex)∈minimalVertices [0,1] repeated ∧
 ([true] : Vertex)∈minimalVertices [2,3] repeated ∧
 agreement repeated repeated (splitForest [0,1] [[0,1,2,3]])=false := by decide

theorem selected_actual_source_edge :
 cuts selectedS 0 1=[[false,false,true]] ∧
 CoreGraph.subtree selectedS [false,false,true]=some (.leaf 2) ∧
 splitForest [2] selectedF=[[2],[0,3,4],[1],[5]] ∧
 agreement selectedT selectedS (splitForest [2] selectedF)=true ∧
 (splitForest [2] selectedF).length=selectedF.length+1 := by decide

theorem selected_split_universal_application :
 agreement selectedT selectedS (splitForest [2] selectedF)=true := by
 exact original_clade_split_agreement selectedT selectedS (.leaf 2) [false,false,true]
  selectedF selected_proper selected_actual_source_edge.2.1 selected_control_forests.1
end ContactedClade
