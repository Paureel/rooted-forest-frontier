import Rule5SourceBounds
namespace Universal233.Rule5ExecutionSource
open RMAF CoreGraph HardParent Rule5PrefixLocalWork
open OrdinaryDispatch.FullSourceWork OrdinaryDispatch.WorkRecursion WholeSourceWork CoreWork GenericForest GenericForest.CheckCorrespondence GenericForest.FrontierWork
open CherryBranching Rule5Case322 Rule5PaidSelector Case322PaidGuard Rule5SelectedLocalWork Rule5RemainingLocalWork Rule5PendantLocalWork Rule5FinalClassification Rule5Classification Rule5OrdinaryDispatch Rule5Local

theorem run_selected_calls_native (cb : Ordinary) (W : OrdinaryWork) (classFee : CheckRequest→Nat)
 (literalFee : LiteralCall→Nat) (T S : Tree) (a b q : Nat) (z : FinalSelection) :
 runSelectedCalls cb W classFee literalFee T S a b q z=
 Rule5ActualTrace.queries cb (Rule5ActualTrace.selectedTrace cb T S a b q z).calls := by
 cases z with
 | «prefix» s=>simp only [runSelectedCalls,childrenTrace,selected_children_value,selectedForestChildren,Rule5ActualTrace.selectedTrace]
 | remaining d z=>cases z with
  | first u v=>simp only [runSelectedCalls,childrenTrace,selected_children_value,selectedForestChildren,Rule5ActualTrace.selectedTrace]
  | third u v=>simp only [runSelectedCalls,childrenTrace,selected_children_value,selectedForestChildren,Rule5ActualTrace.selectedTrace]
  | one e=>simp only [runSelectedCalls,Rule5ActualTrace.selectedTrace,Rule5ActualTrace.queries,Rule5ActualTrace.common_calls]
  | second u v=>
   simp only [runSelectedCalls,solve_selected_calls_native,Rule5ActualTrace.selectedTrace]
   cases buildSelected T S a b <;> rfl

theorem run_selected_query_domain (cb : Ordinary) (W : OrdinaryWork) (classFee : CheckRequest→Nat)
 (literalFee : LiteralCall→Nat) {T S : Tree} {i : RMAF.Vertex} {a b : Nat}
 (ch:CherryAt T i a b) (ad:admitted T S a b=true) {z : FinalSelection}
 (sel:(finalMeter classFee T S a b).value=some z) (q : Nat) {p : Tree×Tree} {r : Nat}
 (mem:(p,r)∈runSelectedCalls cb W classFee literalFee T S a b q z) :
 r<q ∧ DepthOne.proper p.1 p.2=true ∧ (leaves p.1).length≤(leaves T).length ∧ (leaves p.2).length≤(leaves T).length := by
 rw [run_selected_calls_native] at mem
 exact Rule5ActualTrace.selected_query_bounds cb ch ad (by rw [←final_value classFee];exact sel) q mem

theorem dispatch_calls_native (cb : Ordinary) (W : OrdinaryWork) (classFee : CheckRequest→Nat)
 (literalFee : LiteralCall→Nat) (T S : Tree) (a b q : Nat) :
 dispatchCalls cb W classFee literalFee T S a b q=
 Rule5ActualTrace.queries cb (Rule5ActualTrace.dispatchTrace cb T S a b q).calls := by
 cases sel:selectFinal T S a b <;> simp only [dispatchCalls,final_value,sel,run_selected_calls_native,Rule5ActualTrace.dispatchTrace]
 rfl

theorem dispatch_query_domain (cb : Ordinary) (W : OrdinaryWork) (classFee : CheckRequest→Nat)
 (literalFee : LiteralCall→Nat) {T S : Tree} {i : RMAF.Vertex} {a b : Nat}
 (ch:CherryAt T i a b) (ad:admitted T S a b=true) (q : Nat) {p : Tree×Tree} {r : Nat}
 (mem:(p,r)∈dispatchCalls cb W classFee literalFee T S a b q) :
 r<q ∧ DepthOne.proper p.1 p.2=true ∧ (leaves p.1).length≤(leaves T).length ∧ (leaves p.2).length≤(leaves T).length := by
 rw [dispatch_calls_native] at mem
 exact Rule5ActualTrace.dispatch_query_bounds cb ch ad q mem
end Universal233.Rule5ExecutionSource
