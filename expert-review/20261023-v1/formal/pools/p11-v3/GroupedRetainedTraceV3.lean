import OrdinaryChildrenCanonicalValueV3

namespace SourceGroupedRetainsV3
open RMAF Universal233

theorem trace_eq {a b : BothBadGrouped.OutputResult} (h : OutputRetains a b) :
    a.trace=b.trace := by
  cases a <;> cases b <;> simp only [OutputRetains,BothBadGrouped.OutputResult.trace] at h ⊢
  all_goals first | exact h.2 | rfl | trivial | contradiction
end SourceGroupedRetainsV3
