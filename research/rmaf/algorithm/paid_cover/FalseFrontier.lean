import FailedFrontier
open PaidCoverFailedFrontier
set_option maxRecDepth 100000
set_option maxHeartbeats 0
-- Destructive control: expected compiler failure because the finite
-- executable proposition is false. Never import into accepted code.
theorem false_minimum_frontier_preserves_parent :
    optimum (some [[1,2,4],[0,3]]) = some 2 := by
  rw [exact_parent_and_frontier_optima.2.1]
  decide
