import ActualSupportTransport
import Controls
namespace RestrictionRouteUseSites
open RMAF RestrictionRoute RestrictionRouteControls

theorem swapped_root_consumer :
    restrictionAgrees tRoot uRoot [0] = true ∧ restrictionAgrees tRoot uRoot [1] = true ∧
    disjointVertices (minimalVertices [0] uRoot) (minimalVertices [1] uRoot) = true := by
  apply two_block_transport tRoot uRoot [0] [1] [0,1]
  all_goals decide

theorem suppressed_path_consumer :
    restrictionAgrees tPath uPath [0] = true ∧ restrictionAgrees tPath uPath [2] = true ∧
    disjointVertices (minimalVertices [0] uPath) (minimalVertices [2] uPath) = true := by
  apply two_block_transport tPath uPath [0] [2] [0,2]
  all_goals decide

theorem outside_labels_consumer :
    restrictionAgrees tOutside uOutside [0] = true ∧ restrictionAgrees tOutside uOutside [2] = true ∧
    disjointVertices (minimalVertices [0] uOutside) (minimalVertices [2] uOutside) = true := by
  apply two_block_transport tOutside uOutside [0] [2] [0,2]
  all_goals decide

/-- The equality transports an overlapping result too; it does not bless an
arbitrary split as a refinement. -/
theorem overlap_stays_overlap :
    disjointVertices (minimalVertices [0,2] tFour) (minimalVertices [1,3] tFour) = false := by
  have heq := actual_disjoint_transport_eq tFour tFour [0,2] [1,3] [0,1,2,3]
    (by decide) (by decide) (by decide)
  have hfalse : disjointVertices (minimalVertices [0,2] tFour) (minimalVertices [1,3] tFour) = false := by decide
  exact heq ▸ hfalse

#print axioms swapped_root_consumer
#print axioms suppressed_path_consumer
#print axioms outside_labels_consumer
#print axioms overlap_stays_overlap
end RestrictionRouteUseSites
