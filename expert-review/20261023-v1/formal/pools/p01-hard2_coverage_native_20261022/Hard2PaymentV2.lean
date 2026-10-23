-- Exact literal parent charge and source/materialization identity at actual hard2.
import Hard2BackboneCaller
open RMAF ForestState Universal233 Universal233.CherryBranching
open OrdinaryDispatch OrdinaryDispatch.FastOrdinary
namespace ContactedHard2

theorem actual_parent_payment {T S : Tree} {c d : Candidate}
 (proper : DepthOne.proper T S=true) (selected : early T S=.hard2 c d)
 {F : List (List Nat)} (feasible : feasible T S (pendantChild S c.a c.b) F) :
 (pendantChild S c.a c.b).paid=2 ∧
 2+additionalCost (pendantChild S c.a c.b).sourceForest F=F.length-1 := by
 have domain:=actual_hard2_domain proper selected
 have lit:=(actual_backbone_literal proper selected).1 (pendantChild S c.a c.b)
   (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
 have paid : (pendantChild S c.a c.b).paid=2 := by
  change (cuts S c.a c.b).length=2
  rw [←domain.2.1.2.1]
  exact domain.2.1.2.2
 have identity:=IndependentPaid.paid_identity (IndependentReconstruction.proper_parts proper).2.1 lit.1 lit.2.2.1 feasible
 have material:=FreshResidual.residual_transfer_scope.1 T S (pendantChild S c.a c.b).partition [] proper lit.1 lit.2.1
 rw [←lit.2.2.2] at material
 refine ⟨paid,?_⟩
 unfold additionalCost
 rw [material.1,←paid]
 exact identity
end ContactedHard2

-- Author integration type/axiom reports; proof text above is unchanged apart from recorded import edits.
set_option pp.universes true
#check @ContactedHard2.actual_parent_payment
#print axioms ContactedHard2.actual_parent_payment
