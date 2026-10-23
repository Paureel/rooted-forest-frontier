import LiteralSchedulerRawProjectionV3

namespace SourceRule5CanonicalV3
open RMAF Universal233 SourceForestV3
open OrdinaryDispatch.WorkRecursion

-- Equality of the two separately bound computations, not a declaration alias.
theorem children_equal (actual : GenericForest.FrontierWork.Ordinary)
    (T S : Tree) (q : Nat) (cs : List CherryBranching.Child) :
    OrdinaryDispatch.runChildren actual T S q cs=Rule5OrdinaryDispatch.runChildren actual T S q cs := rfl

theorem forest_jobs_value (actual : GenericForest.FrontierWork.Ordinary)
    (T S : Tree) (q : Nat) (cs : List CherryBranching.Child) :
    Rule5ActualTrace.runForestJobs actual T S q (Rule5OrdinaryDispatch.forestJobs T q cs)=
      Rule5OrdinaryDispatch.runChildren actual T S q cs := by
  have hv:=children_trace_parent_value actual T S q cs
  rw [children_equal] at hv
  exact hv

theorem paid_best_value (actual : GenericForest.FrontierWork.Ordinary)
    {T S : Tree} (R : Rule5PaidSelector.SelectedPaid T S) (q : Nat) :
    Rule5ActualTrace.runPaidRequests actual T S q (Rule5PaidSelector.requests R.geometry q)=
      Rule5PaidOrdinary.bestFor actual R q := by
  rfl
end SourceRule5CanonicalV3
