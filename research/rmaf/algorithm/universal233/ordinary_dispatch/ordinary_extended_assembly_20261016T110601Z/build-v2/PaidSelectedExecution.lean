import PaidExecutionBounds
namespace Universal233.Rule5ExecutionSource
open RMAF CoreGraph HardParent Rule5PrefixLocalWork
open OrdinaryDispatch.EarlyLocalWork OrdinaryDispatch.FullSourceWork OrdinaryDispatch.WorkRecursion WholeSourceWork CoreWork GenericForest GenericForest.CheckCorrespondence GenericForest.FrontierWork
open CherryBranching Rule5Case322 Rule5PaidSelector Case322PaidGuard Rule5SelectedLocalWork Rule5RemainingLocalWork Rule5PendantLocalWork Rule5FinalClassification Rule5Classification

def paidExecutionPrefixBudget (T S : Tree) (Kc Kl : Nat) :=
 paidSelectedBudget (leaves T).length (leaves S).length Kc Kl+
 paidBestBudget T S (2*((leaves T).length+(leaves S).length)) ((leaves T).length+(leaves S).length)+2

theorem solve_selected_prefix_work (cb : Ordinary) (W : OrdinaryWork) (classFee : CheckRequest→Nat)
 (literalFee : LiteralCall→Nat) (T S : Tree) (a b q L Kc Kl : Nat)
 (tlabs : ∀x,x∈leaves T→x<2^L) (slabs : ∀x,x∈leaves S→x<2^L)
 (classifier : ∀r,CheckDomain ((leaves T).length+(leaves S).length) L r→classFee r≤Kc)
 (literal : ∀d u v,(finalMeter classFee T S a b).value=some (.remaining d (.second u v))→
  ∀j,LiteralCallDomain T S a b d u v j→literalFee j≤Kl) :
 (solveSelectedMeter cb W classFee literalFee T S a b q).prefixWork≤paidExecutionPrefixBudget T S Kc Kl := by
 have p:=paid_selected_work classFee literalFee T S a b L Kc Kl tlabs slabs classifier literal
 have tn:=treeNodes_le_twice_leaves T;have sn:=treeNodes_le_twice_leaves S
 cases hp:(paidSelectedMeter classFee literalFee T S a b).value with
 | none=>simp only [solveSelectedMeter,hp];unfold paidExecutionPrefixBudget;omega
 | some R=>
  have built:buildSelected T S a b=some R:=by rw [←paid_selected_value classFee literalFee];exact hp
  have b:=best_for_prefix_work cb W built q (2*((leaves T).length+(leaves S).length))
    ((leaves T).length+(leaves S).length) (by omega) (by omega) (by omega) (by omega) (by omega)
  simp only [solveSelectedMeter,hp,paidExecutionPrefixBudget];omega

theorem solve_selected_calls_native (cb : Ordinary) (W : OrdinaryWork) (classFee : CheckRequest→Nat)
 (literalFee : LiteralCall→Nat) (T S : Tree) (a b q : Nat) :
 (solveSelectedMeter cb W classFee literalFee T S a b q).ordinaryCalls=
 match buildSelected T S a b with
 | none=>[]
 | some R=>Rule5ActualTrace.queries cb (.paidRequests (requests R.geometry q)) := by
 cases hp:(paidSelectedMeter classFee literalFee T S a b).value <;>
 simp only [solveSelectedMeter,hp,←paid_selected_value classFee literalFee T S a b,bestForMeter,answers_calls_native]
end Universal233.Rule5ExecutionSource
