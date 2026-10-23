import GraphControls
namespace OrdinaryCommonSplit.GraphControls
open RMAF Universal233
theorem false_unstable_still_free : commonSplitValue 0 0 1 1=0 := by decide
theorem false_mixed_root_zero : sameShape rootT rootS=true := by decide
theorem false_no_marker_topology_change : sameShape markedXTree markedXOther=true := by decide
theorem false_missing_marker_freshness :
    (marked (.node (.leaf 0) (.leaf 1)) [0] 1 0).any
      (fun t => decide ((leaves t).Perm [0,0]))=true := by decide
end OrdinaryCommonSplit.GraphControls
