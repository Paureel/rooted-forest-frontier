-- Exact complete three-child backbone; specialized Hard2Dispatcher.run remains open.
import Hard2BackboneGeometryV2
open RMAF ForestState Universal233 Universal233.CherryBranching
open OrdinaryDispatch OrdinaryDispatch.FastOrdinary
namespace ContactedHard2

theorem actual_backbone_callbacks (ordinary : PaidInstances.OrdinarySolver) (q : Nat)
 {T S : Tree} {c d : Candidate} (proper : DepthOne.proper T S=true)
 (selected : early T S=.hard2 c d) (below : PaidInstances.BelowBudget ordinary q) :
 IndependentPaid.CurrentChildren (PaidInstances.OwnPaid ordinary q) T S q (branches S c.a c.b) := by
 have ready:=actual_backbone_literal proper selected
 intro child member r remaining
 obtain ⟨partition,embeddings,_,material⟩:=ready.1 child member
 have strict:=IndependentPaid.remaining_strict (ready.2 child member) remaining
 have ih:=PaidInstances.local_ordinary_ih ordinary q r below strict
 have scope:=FreshResidual.residual_transfer_scope.1 T S child.partition [] proper partition embeddings
 rw [←material] at scope
 apply PaidInstances.exact_child_of_materialized (PaidInstances.OwnPaid ordinary q) T S child r ih scope.1
 intro F
 have bound:=FreshResidual.residual_transfer_scope.1 T S child.partition F proper partition embeddings
 rw [←material] at bound
 exact bound.2.2

theorem actual_backbone_query (ordinary : PaidInstances.OrdinarySolver) (q : Nat)
 {T S : Tree} {c d : Candidate} (proper : DepthOne.proper T S=true)
 (selected : early T S=.hard2 c d) (below : PaidInstances.BelowBudget ordinary q) :
 QueryExact T S q (runChildren (PaidInstances.OwnPaid ordinary q) T S q (branches S c.a c.b)) := by
 have ready:=actual_backbone_literal proper selected
 have cover : IndependentPaid.Coverage T S (branches S c.a c.b) := by
  intro F agree
  obtain ⟨child,member,feasible⟩:=actual_three_child_cover proper selected F agree
  exact ⟨child,member,F,feasible,Nat.le_refl _⟩
 exact IndependentPaid.caller_query _ T S q _ (IndependentReconstruction.proper_parts proper).2.1
   ready.1 (actual_backbone_callbacks ordinary q proper selected below) cover

theorem actual_backbone_printed : ∀ordinary q T S c d,
 DepthOne.proper T S=true → DepthOne.pretest01 T S=.rejected → early T S=.hard2 c d →
 PaidInstances.BelowBudget ordinary q →
 QueryExact T S q (runChildren (PaidInstances.OwnPaid ordinary q) T S q (branches S c.a c.b)) := by
 intro ordinary q T S c d proper _ selected below
 exact actual_backbone_query ordinary q proper selected below

#print actual_backbone_printed
#print axioms actual_backbone_printed
end ContactedHard2

-- Author integration type/axiom reports; proof text above is unchanged apart from recorded import edits.
set_option pp.universes true
#check @ContactedHard2.actual_backbone_callbacks
#print axioms ContactedHard2.actual_backbone_callbacks
#check @ContactedHard2.actual_backbone_query
#print axioms ContactedHard2.actual_backbone_query
#check @ContactedHard2.actual_backbone_printed
#print axioms ContactedHard2.actual_backbone_printed
