import ResidualBudget
namespace FreshResidual
open RMAF ForestState OutputState Universal233.CherryBranching

theorem residual_transfer_scope :
 (∀(T S : Tree) (P F : List (List Nat)),
   Universal233.DepthOne.proper T S=true →
   partitionCheck (leaves S) P=true → pairwiseEmbeddings S P=true →
   (sourceForest S P).length=P.length ∧
   ForestState.proper (some T) (sourceForest S P)=true ∧
   (ForestState.agrees (some T) (sourceForest S P) F=true ↔
    agreement T S F=true ∧ VertexGeometry.Refines F P)) ∧
 (∀(T S : Tree) (c : Child) (q r : Nat),
   Universal233.DepthOne.proper T S=true →
   partitionCheck (leaves S) c.partition=true → pairwiseEmbeddings S c.partition=true →
   c.sourceForest=sourceForest S c.partition →
   c.paid+1=c.partition.length → remaining q c=some r →
   ((∃F,feasible T S c F ∧ F.length-1≤q) ↔
    ∃F,ForestState.agrees (some T) c.sourceForest F=true ∧ additionalCost c.sourceForest F≤r)) ∧
 (∀(T S : Tree) (c : Child) (r : Nat),
   Universal233.DepthOne.proper T S=true →
   partitionCheck (leaves S) c.partition=true → pairwiseEmbeddings S c.partition=true →
   c.sourceForest=sourceForest S c.partition →
   (ChildWithin T S c r ↔
    ∃F,ForestState.agrees (some T) c.sourceForest F=true ∧ additionalCost c.sourceForest F≤r)) := by
 refine ⟨?_,?_,?_⟩
 · intro T S P F proper pp ep
   have ns : (leaves S).Nodup := by
     simp only [Universal233.DepthOne.proper,Bool.and_eq_true,decide_eq_true_eq] at proper
     exact proper.1.2
   exact ⟨sourceForest_length ns pp,sourceForest_proper proper pp,original_materialized_iff proper pp ep⟩
 · intro T S c q r proper pp ep source bill rem
   exact paid_residual_exists_iff proper pp ep source bill rem
 · intro T S c r proper pp ep source
   exact childWithin_materialized_iff proper pp ep source

#print axioms residual_transfer_scope
end FreshResidual

-- Author integration type/axiom reports; proof text above is unchanged apart from recorded import edits.
set_option pp.universes true
#check @FreshResidual.residual_transfer_scope
#print axioms FreshResidual.residual_transfer_scope
