import ActualCommonLift
open RMAF ForestState Universal233 Universal233.HardParent
namespace IndependentGeometry

theorem expansion_control :
 let T := Tree.node (.node (.leaf 0) (.leaf 1)) (.leaf 2)
 let U := Tree.node (.leaf 2) (.node (.leaf 1) (.leaf 0))
 agreement T U ([[3],[2]].map (expandBlock 0 1 3))=true := by decide

theorem separate_singleton_control :
 let T := Tree.node (.node (.leaf 0) (.leaf 1)) (.leaf 2)
 let U := Tree.node (.leaf 2) (.node (.leaf 1) (.leaf 0))
 agreement T U [[0,2],[1]]=true ∧
 coarsen 0 1 3 [[0,2],[1]]=[[3,2]] ∧
 agreement (contract 0 1 3 T) (contract 0 1 3 U) (coarsen 0 1 3 [[0,2],[1]])=true := by decide

theorem separate_nonsingleton_control :
 let T := Tree.node (.node (.leaf 0) (.leaf 1)) (.leaf 2)
 let U := Tree.node (.leaf 2) (.node (.leaf 1) (.leaf 0))
 agreement T U [[0],[1,2]]=true ∧ coarsen 0 1 3 [[0],[1,2]]=[[3],[2]] ∧
 agreement (contract 0 1 3 T) (contract 0 1 3 U) (coarsen 0 1 3 [[0],[1,2]])=true := by decide

theorem same_block_control : coarsen 0 1 3 [[0,1],[2]]=[[3],[2]] := by decide

theorem missing_endpoint_rejected :
 let T := Tree.node (.node (.leaf 0) (.leaf 1)) (.leaf 2)
 let U := Tree.node (.leaf 2) (.node (.leaf 1) (.leaf 0))
 agreement T U [[0],[2]]=false := by decide

theorem overlap_despite_partition_and_shapes :
 let T := Tree.node (.node (.leaf 0) (.leaf 1)) (.node (.leaf 2) (.leaf 3))
 let F := [[0,2],[1,3]]
 partitionCheck (leaves T) F=true ∧ F.all (restrictionAgrees T T)=true ∧ agreement T T F=false := by decide

theorem identity_vertex_lift_refuted :
 let T := Tree.node (.node (.leaf 0) (.leaf 1)) (.leaf 2)
 let C := contract 0 1 3 T
 ¬(∀v∈minimalVertices (shrinkBlock 0 1 3 [0]) C,v∈minimalVertices [0] T) := by decide
end IndependentGeometry
