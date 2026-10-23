import RawIncursion
open TripleDP.Transitions.Restriction
open TripleDP.Transitions.Restriction.NormalizedRoute
open TripleDP.Transitions.Restriction.NormalizedRoute.Controls
theorem false_raw_premise : OpenBranchLive assembled := by
  exact normalized_open_openBranchLive raw incursion rfl raw_live
