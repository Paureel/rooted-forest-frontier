import Hard2SourceBill
import Hard2Controls
namespace OrdinaryDispatch.WorkIntegration.Controls
open RMAF ForestState Universal233 Universal233.BothBad
open OrdinaryDispatch.Hard2Dispatcher GenericForest.FrontierWork

def failedCalls : List Call :=
 [⟨some Hard2Dispatcher.Controls.T,[Hard2Dispatcher.Controls.S],2⟩,
  ⟨some Hard2Dispatcher.Controls.T,[Hard2Dispatcher.Controls.S],2⟩]

theorem repeated_failed_frontier : (forestQueries Hard2Dispatcher.Controls.refusal failedCalls).length=2 := by cbv
theorem full_actual_value :
 (hard2Trace Hard2Dispatcher.Controls.ActualFirst.hostile Rule5Local.Pre.commonT Rule5Local.Pre.commonS
  Hard2Dispatcher.Controls.ActualFirst.c Hard2Dispatcher.Controls.ActualFirst.d 0).value=none := by
 rw [hard2Trace_value]
 exact Hard2Dispatcher.Controls.ActualFirst.no_zero_budget_fabrication

theorem actual_nonadmitted_full_mass (q : Nat) :
 Rule5ActualTrace.mass Rule5ActualTrace.base q
  (hard2Trace Hard2Dispatcher.Controls.ActualFirst.hostile Rule5Local.Pre.commonT Rule5Local.Pre.commonS
  Hard2Dispatcher.Controls.ActualFirst.c Hard2Dispatcher.Controls.ActualFirst.d q).queries≤
 Rule5ActualTrace.gamma Rule5ActualTrace.base := by
 have facts := Hard2Dispatcher.Controls.ActualFirst.priority_and_graph
 exact hard2Trace_mass _ q facts.1 facts.2.1 facts.2.2.1 facts.2.2.2.1 facts.2.2.2.2.1

theorem actual_nonadmitted_query_bounds (q : Nat) (p : Tree×Tree) (r : Nat)
 (mem : (p,r)∈(hard2Trace Hard2Dispatcher.Controls.ActualFirst.hostile Rule5Local.Pre.commonT Rule5Local.Pre.commonS
  Hard2Dispatcher.Controls.ActualFirst.c Hard2Dispatcher.Controls.ActualFirst.d q).queries) :
 r<q ∧ DepthOne.proper p.1 p.2=true ∧
 (leaves p.1).length≤(leaves Rule5Local.Pre.commonT).length ∧
 (leaves p.2).length≤(leaves Rule5Local.Pre.commonT).length := by
 have facts := Hard2Dispatcher.Controls.ActualFirst.priority_and_graph
 exact hard2Trace_query_bounds _ q facts.1 facts.2.1 facts.2.2.1 facts.2.2.2.1 facts.2.2.2.2.1 p r mem

theorem literal_coefficient : forestCoefficient 1 0=((2^50*3^8:Nat):Rat) := rfl
end OrdinaryDispatch.WorkIntegration.Controls
