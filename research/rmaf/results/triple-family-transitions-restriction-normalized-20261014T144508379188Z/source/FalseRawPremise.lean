import RawIncursion
open TripleDP.Transitions.Restriction
open TripleDP.Transitions.Restriction.NormalizedRoute.Controls
theorem false_raw_premise : OpenBranchLive assembled := by
  exact raw_not_openBranchLive
