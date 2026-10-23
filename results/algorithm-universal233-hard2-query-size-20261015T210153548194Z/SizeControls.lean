import PaidTargets
import Hard2Controls
namespace OrdinaryDispatch.Hard2Size.Controls
open RMAF ForestState ForestGroups Universal233 Universal233.BothBad OrdinaryDispatch.Hard2Dispatcher

def target : Tree := .node (.node (.leaf 0) (.leaf 1)) (.node (.leaf 2) (.leaf 3))
theorem restricted_current_topology : localTarget (some target) [0,3]=some (.node (.leaf 0) (.leaf 3)) := by decide
theorem restricted_current_size : (labels (localTarget (some target) [0,3])).length=2 := by decide
theorem absent_query_empty : localTarget (some target) [9]=none ∧ (labels (localTarget (some target) [9])).length=0 := by decide
theorem original_target_size : (labels (some target)).length=4 := rfl

theorem actual_nonadmitted_target (q : Nat) (call : Call)
 (mem : call∈(Hard2Combine.combine OrdinaryDispatch.Hard2Dispatcher.Controls.ActualFirst.hostile
 Rule5Local.Pre.commonT Rule5Local.Pre.commonS OrdinaryDispatch.Hard2Dispatcher.Controls.ActualFirst.c.a
 OrdinaryDispatch.Hard2Dispatcher.Controls.ActualFirst.c.b q
 (paidCase OrdinaryDispatch.Hard2Dispatcher.Controls.ActualFirst.hostile Rule5Local.Pre.commonT
 Rule5Local.Pre.commonS OrdinaryDispatch.Hard2Dispatcher.Controls.ActualFirst.c q (.pair .acb (.vertex [false,false,false])))).calls) :
 TargetBound Rule5Local.Pre.commonT call.target ∧
 (labels call.target).length+2*call.budget+2≤(leaves Rule5Local.Pre.commonT).length+2*q := by
 have facts := OrdinaryDispatch.Hard2Dispatcher.Controls.ActualFirst.priority_and_graph
 exact ⟨combined_target_bound _ _ _ _ q _ call mem,
  combined_query_potential _ facts.1 facts.2.1 facts.2.2.2.2.2.2.2 call mem⟩
end OrdinaryDispatch.Hard2Size.Controls
