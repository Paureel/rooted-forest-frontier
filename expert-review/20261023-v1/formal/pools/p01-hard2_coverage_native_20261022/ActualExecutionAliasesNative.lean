import OrdinaryExecution34
open RMAF Universal233 PaidQueries RestrictionBridge FreshOrdinaryBridge
set_option autoImplicit false
namespace ActualOrdinaryExecution

theorem contract :
 ∀ (outer b : Nat) (below : IndependentReconstruction.BelowBudget outer)
    (hb : b<outer) (T S : Tree) (Q : List (List Nat))
    (pt : (leaves T).Nodup) (ps : (leaves S).Nodup)
    (hQT : partitionCheck (leaves T) Q=true) (hQS : partitionCheck (leaves S) Q=true)
    (eT : pairwiseEmbeddings T Q=true) (eS : pairwiseEmbeddings S Q=true),
 ParentQueryExact T S Q b
      (BothBad.ordinaryExecution (GenericForest.solve (IndependentReconstruction.OwnPaid outer)) T S Q b).answer ∧
    ∀c∈(BothBad.ordinaryExecution (GenericForest.solve (IndependentReconstruction.OwnPaid outer)) T S Q b).calls,
      c.budget<outer := FreshOrdinaryBridge.execution_contract

theorem literal_parent_contract :
 ∀ (outer : Nat) (below : IndependentReconstruction.BelowBudget outer)
    (T S : Tree) (Q : List (List Nat))
    (pt : (leaves T).Nodup) (ps : (leaves S).Nodup)
    (hQT : partitionCheck (leaves T) Q=true) (hQS : partitionCheck (leaves S) Q=true)
    (eT : pairwiseEmbeddings T Q=true) (eS : pairwiseEmbeddings S Q=true)
    (hpay : Q.length-1≤outer) (hparents : 2≤Q.length),
 ParentQueryExact T S Q (outer-(Q.length-1))
      (BothBad.ordinaryExecution (GenericForest.solve (IndependentReconstruction.OwnPaid outer))
        T S Q (outer-(Q.length-1))).answer ∧
    ∀c∈(BothBad.ordinaryExecution (GenericForest.solve (IndependentReconstruction.OwnPaid outer))
      T S Q (outer-(Q.length-1))).calls,c.budget<outer := FreshOrdinaryBridge.literal_parent_contract

theorem literal_output_payment :
 ∀ (outer : Nat) (T S : Tree) (Q F : List (List Nat))
    (hQS : partitionCheck (leaves S) Q=true) (hparents : 1≤Q.length)
    (hpay : Q.length-1≤outer) (hAF : agreement T S F=true) (href : Refines F Q)
    (hlocal : F.length-Q.length≤outer-(Q.length-1)),
 F.length-1=(Q.length-1)+(F.length-Q.length) ∧ F.length-1≤outer := FreshOrdinaryBridge.literal_output_payment

theorem singleton_callback_exact :
 ∀ (outer r : Nat) (hstrict : r<outer)
    (below : IndependentReconstruction.BelowBudget outer) (T S : Tree)
    (hp : DepthOne.proper T S=true),
 OrdinaryDispatch.QueryExact T S r
      (BothBad.asTree (GenericForest.solve (IndependentReconstruction.OwnPaid outer)) T S r) := FreshOrdinaryBridge.singleton_callback_exact

end ActualOrdinaryExecution
#check @ActualOrdinaryExecution.contract
#print axioms ActualOrdinaryExecution.contract
#check @ActualOrdinaryExecution.literal_parent_contract
#print axioms ActualOrdinaryExecution.literal_parent_contract
#check @ActualOrdinaryExecution.literal_output_payment
#print axioms ActualOrdinaryExecution.literal_output_payment
#check @ActualOrdinaryExecution.singleton_callback_exact
#print axioms ActualOrdinaryExecution.singleton_callback_exact
