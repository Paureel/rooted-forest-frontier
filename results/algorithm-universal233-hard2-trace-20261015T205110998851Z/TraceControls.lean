import TraceProgress
import Hard2Controls
namespace OrdinaryDispatch.Hard2Trace.Controls
open RMAF Universal233 Universal233.BothBad OrdinaryDispatch.Hard2Dispatcher

def failedCalls : List Call := [⟨some (.leaf 0),[.leaf 0],1⟩,⟨some (.leaf 0),[.leaf 0],1⟩]
theorem repeated_failed_queries_counted : traceMass 2 4 failedCalls=1/4 := by cbv
theorem literal_residual_debit : traceMass 2 4 [⟨some (.leaf 0),[.leaf 0],1⟩]=1/8 := by cbv
theorem exact_uniform_contraction :
 2*(233/100 : Rat)^(-1 : Int)+4*(233/100 : Rat)^(-4 : Int)<1 := exact_233_contraction
theorem boundary_not_contractive : 2*(2 : Rat)^(-1 : Int)+4*(2 : Rat)^(-4 : Int)=5/4 := by cbv

theorem actual_nonadmitted_progress (q : Nat) (call : Call)
 (mem : call∈(paidCase OrdinaryDispatch.Hard2Dispatcher.Controls.ActualFirst.hostile
 Rule5Local.Pre.commonT Rule5Local.Pre.commonS OrdinaryDispatch.Hard2Dispatcher.Controls.ActualFirst.c q
 (.pair .acb (.vertex [false,false,false]))).calls) : call.budget+2≤q ∧ call.budget<q := by
 have facts := OrdinaryDispatch.Hard2Dispatcher.Controls.ActualFirst.priority_and_graph
 exact paidCase_calls_drop _ facts.1 facts.2.1 facts.2.2.2.2.2.2.2 call mem
end OrdinaryDispatch.Hard2Trace.Controls
