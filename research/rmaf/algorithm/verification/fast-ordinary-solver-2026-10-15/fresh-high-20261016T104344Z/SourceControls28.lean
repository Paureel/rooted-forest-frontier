-- Supplemental source-only controls; authored after the source reduction,
-- so these are development controls, not a new independent acceptance leg.
import Boundary26
import Controls13
open RMAF Universal233
namespace OwnHigh
def T3 := Tree.node T0 (.node (.leaf 2) (.leaf 3))
def S3 := Tree.node (.node (.node (.leaf 0) (.leaf 2)) (.leaf 3)) (.leaf 1)
theorem source_high_two : DepthOne.proper T3 S3 = true ∧
    CoreGraph.CherryAt T3 [false] 0 1 ∧ agreement T3 S3 [[0,1],[2],[3]] = true ∧
    (CherryBranching.cuts S3 0 1).length = 2 ∧
    CherryBranching.pendantPartition S3 0 1 = [[2],[3],[0,1]] ∧
    refinesB [[0,1],[2],[3]] [[2],[3],[0,1]] = true := by unfold CoreGraph.CherryAt; decide
theorem source_high_two_no_cross : NoPendantCrossing S3 0 1 [[0,1],[2],[3]] := by
  simp [NoPendantCrossing, CherryBranching.cuts, HardParent.pendantOriginal,
    HardParent.vertices, minimalVertices, rootedSpan, prependSide, HardParent.subtreeLabels,
    S3, leaves]
#print axioms source_high_two
#print axioms source_high_two_no_cross
end OwnHigh
