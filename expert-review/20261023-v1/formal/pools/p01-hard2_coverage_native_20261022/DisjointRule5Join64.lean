import DisjointMixedCorrectness60
open RMAF Universal233 CherryBranching OrdinaryDispatch RestrictionBridge
set_option autoImplicit false
namespace FreshLiteralDisjoint
theorem actual_disjoint_rule5_route (actual : DisjointParents.Ordinary) (T S : Tree)
 (c d : Candidate) (q : Nat) (picked : Hard2Overlap.runHard2 T S c=some .disjoint)
 (good : (pendantPartition S c.a c.b).all (restrictionAgrees T S)=false)
 (two : ((pendantPartition S c.a c.b).filter (restrictionAgrees T S)).length=2) :
 Hard2Dispatcher.run actual T S c d q=Hard2Dispatcher.rule5Answer actual T S c.a c.b q := by
 unfold Hard2Dispatcher.run
 rw [picked]
 simp only [Hard2Dispatcher.run.match_1,Hard2Dispatcher.run._sparseCasesOn_1,good,two]
 rfl

/-- Exact remaining literal Rule5 consumer, not an established premise. -/
def DisjointRule5Clause : Prop := ∀q T S c d,
 DepthOne.proper T S=true → DepthOne.pretest01 T S=.rejected →
 FastOrdinary.early T S=.hard2 c d → Hard2Overlap.runHard2 T S c=some .disjoint →
 IndependentReconstruction.BelowBudget q →
 (pendantPartition S c.a c.b).all (restrictionAgrees T S)=false →
 ((pendantPartition S c.a c.b).filter (restrictionAgrees T S)).length=2 →
 QueryExact T S q (Hard2Dispatcher.rule5Answer (IndependentReconstruction.OwnPaid q) T S c.a c.b q)

/-- Restriction of the original Hard2Rule consumer to actual selected-disjoint inputs. -/
def DisjointHard2Rule : Prop := ∀q T S c d,
 DepthOne.proper T S=true → DepthOne.pretest01 T S=.rejected →
 FastOrdinary.early T S=.hard2 c d → IndependentReconstruction.BelowBudget q →
 Hard2Overlap.runHard2 T S c=some .disjoint →
 QueryExact T S q (Hard2Dispatcher.run (IndependentReconstruction.OwnPaid q) T S c d q)

theorem original_disjoint_hard2_with_rule5 (q : Nat) (T S : Tree) (c d : Candidate)
 (proper : DepthOne.proper T S=true) (pretest : DepthOne.pretest01 T S=.rejected)
 (selected : FastOrdinary.early T S=.hard2 c d)
 (picked : Hard2Overlap.runHard2 T S c=some .disjoint)
 (below : IndependentReconstruction.BelowBudget q)
 (rule5 : (pendantPartition S c.a c.b).all (restrictionAgrees T S)=false →
   ((pendantPartition S c.a c.b).filter (restrictionAgrees T S)).length=2 →
   QueryExact T S q (Hard2Dispatcher.rule5Answer (IndependentReconstruction.OwnPaid q) T S c.a c.b q)) :
 QueryExact T S q (Hard2Dispatcher.run (IndependentReconstruction.OwnPaid q) T S c d q) := by
 cases good : (pendantPartition S c.a c.b).all (restrictionAgrees T S) with
 | true => exact original_all_good_query_exact q T S c d proper pretest selected picked good
 | false =>
  by_cases two : ((pendantPartition S c.a c.b).filter (restrictionAgrees T S)).length=2
  · exact Eq.mp (congrArg (QueryExact T S q)
      (actual_disjoint_rule5_route (IndependentReconstruction.OwnPaid q) T S c d q picked good two).symm)
      (rule5 good two)
  · exact original_mixed_query_exact q T S c d proper selected picked below good two

theorem original_disjoint_rule_of_rule5 (rule5 : DisjointRule5Clause) : DisjointHard2Rule := by
 intro q T S c d proper pretest selected below picked
 exact original_disjoint_hard2_with_rule5 q T S c d proper pretest selected picked below
  (rule5 q T S c d proper pretest selected picked below)
end FreshLiteralDisjoint
#print axioms FreshLiteralDisjoint.actual_disjoint_rule5_route
#print axioms FreshLiteralDisjoint.original_disjoint_hard2_with_rule5
#print axioms FreshLiteralDisjoint.original_disjoint_rule_of_rule5

-- Author integration type/axiom reports; proof text above is unchanged apart from recorded import edits.
set_option pp.universes true
#check @FreshLiteralDisjoint.actual_disjoint_rule5_route
#print axioms FreshLiteralDisjoint.actual_disjoint_rule5_route
#check @FreshLiteralDisjoint.original_disjoint_hard2_with_rule5
#print axioms FreshLiteralDisjoint.original_disjoint_hard2_with_rule5
#check @FreshLiteralDisjoint.original_disjoint_rule_of_rule5
#print axioms FreshLiteralDisjoint.original_disjoint_rule_of_rule5
