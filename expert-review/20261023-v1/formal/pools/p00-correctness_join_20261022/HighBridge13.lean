-- Reused completed residual transfer, composed into the actual high consumer fields.
-- Zero independent/blind/reconstruction credit for the residual/high packages.
import ForestComplete12
import HighConsumer31
import ResidualTransfer
open RMAF ForestState OutputState Universal233 Universal233.CherryBranching
open OrdinaryDispatch OrdinaryDispatch.FastOrdinary
namespace ForestContinuation

-- Exact saved local specialization, absent from the selected Hard2 provider's
-- ForestComplete12 reporting surface. Both consume the same bounded theorem.
theorem forest_completion_obligation : HighCompletion.ForestCompletionObligation := by
 intro r actual ho
 exact forest_complete_local r actual ho r (Nat.le_refl r)

theorem child_state_bridge (T S : Tree) (c : Child)
 (proper : DepthOne.proper T S=true)
 (pp : partitionCheck (leaves S) c.partition=true)
 (ep : pairwiseEmbeddings S c.partition=true)
 (source : c.sourceForest=sourceForest S c.partition)
 (bill : c.paid+1=c.partition.length) : HighCompletion.ChildStateBridge T S c := by
 have ag : ∀F,ForestState.agrees (some T) c.sourceForest F=true ↔
     agreement T S F=true ∧ VertexGeometry.Refines F c.partition := by
   intro F
   rw [source]
   exact FreshResidual.original_materialized_iff proper pp ep
 have cost : ∀F,additionalCost c.sourceForest F=F.length-c.partition.length :=
   fun F=>FreshResidual.literal_additionalCost proper pp source
 constructor
 · intro F hF
   exact ((ag F).mp hF).1
 · intro q F paid hF hcost
   have hcost' := hcost
   rw [cost F] at hcost'
   omega
 · intro q G hG href hbudget
   have pG : partitionCheck (leaves S) G=true := by
     have h:=hG
     simp only [agreement,Bool.and_eq_true] at h
     exact h.1.1.1.2
   have len:=FreshResidual.refinement_length pp pG href
   refine ⟨by omega,(ag G).mpr ⟨hG,href⟩,?_⟩
   rw [cost G]
   omega

theorem high_state_bridge : HighCompletion.HighStateBridge := by
 intro T S reverse c proper early child hc
 have oriented:=(HighSelector.high_selector_facts T S reverse c proper early).1
 have facts:=HighSelector.high_actual_children T S reverse c proper early child hc
 apply child_state_bridge _ _ child oriented facts.1 facts.2.1
 · simpa only [sourceForest] using facts.2.2.1
 · exact facts.2.2.2.1.symm

theorem high_rule (ordinary : HighCompletion.OrdinarySolver) : HighCompletion.HighRuleFor ordinary :=
 HighCompletion.high_rule_consumer ordinary forest_completion_obligation high_state_bridge

#print axioms child_state_bridge
#print axioms high_state_bridge
#print axioms high_rule
end ForestContinuation
