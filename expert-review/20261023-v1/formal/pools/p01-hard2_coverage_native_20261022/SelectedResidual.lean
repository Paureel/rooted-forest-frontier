/- Explicitly licensed completed residual theorem reused with its qualification. -/
import LiteralOneV3
import ResidualTransfer
open RMAF ForestState OutputState Universal233 Universal233.HardParent Universal233.CherryBranching
open OrdinaryDispatch OrdinaryDispatch.FastOrdinary IndependentOneExchange ContactedRepair ContactedSource
namespace ContactedOneConsumer

theorem selected_materialized_scope {T S : Tree} {reverse : Bool} {c : Candidate}
 (proper : DepthOne.proper T S=true) (selected : early T S=.one reverse c) :
 let A := (Oriented reverse T S).1
 let B := (Oriented reverse T S).2
 let child := pendantChild B c.a c.b
 child.sourceForest.length=child.partition.length ∧ ForestState.proper (some A) child.sourceForest=true ∧
 (∀F,ForestState.agrees (some A) child.sourceForest F=true ↔ feasible A B child F) ∧
 (∀q r,remaining q child=some r→
  ((∃F,feasible A B child F ∧ F.length-1≤q) ↔
   ∃F,ForestState.agrees (some A) child.sourceForest F=true ∧ additionalCost child.sourceForest F≤r)) ∧
 (∀r,ChildWithin A B child r ↔
   ∃F,ForestState.agrees (some A) child.sourceForest F=true ∧ additionalCost child.sourceForest F≤r) := by
 have domain := actual_one_domain proper selected
 have lit := pendant_literal_checks domain.1 domain.2.1 domain.2.2.2
 have source := lit.2.2.1
 have bridge := FreshResidual.residual_transfer_scope
 have material := bridge.1 _ _ _ [] domain.1 lit.1 lit.2.1
 rw [←source] at material
 refine ⟨material.1,material.2.1,?_,?_,?_⟩
 · intro F
   have spec := bridge.1 _ _ _ F domain.1 lit.1 lit.2.1
   rw [←source] at spec
   exact spec.2.2
 · intro q r rem
   exact bridge.2.1 _ _ _ q r domain.1 lit.1 lit.2.1 source lit.2.2.2.1 rem
 · intro r
   exact bridge.2.2 _ _ _ r domain.1 lit.1 lit.2.1 source
end ContactedOneConsumer

-- Author integration type/axiom reports; proof text above is unchanged apart from recorded import edits.
set_option pp.universes true
#check @ContactedOneConsumer.selected_materialized_scope
#print axioms ContactedOneConsumer.selected_materialized_scope
