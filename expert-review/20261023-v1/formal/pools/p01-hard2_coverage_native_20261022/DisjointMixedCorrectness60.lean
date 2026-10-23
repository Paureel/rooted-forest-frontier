import DisjointCohabitRefinement56
import UnitOriginal02
open RMAF Universal233 CherryBranching OrdinaryDispatch RestrictionBridge
set_option autoImplicit false
namespace FreshLiteralDisjoint
/-- The actual parent query covers the exact cohabiting competitors required by
unit/paid composition. Its correctness and callback premise are supplied by BelowBudget. -/
theorem original_cohabiting_parent_cover (q : Nat) (T S : Tree) (c d : Candidate)
 (proper : DepthOne.proper T S=true) (selected : FastOrdinary.early T S=.hard2 c d)
 (picked : Hard2Overlap.runHard2 T S c=some .disjoint)
 (below : IndependentReconstruction.BelowBudget q) :
 UnitPaidCombination.CohabitingPaidCover T S c q
  (DisjointParents.query (IndependentReconstruction.OwnPaid q) T S (pendantPartition S c.a c.b) q) := by
 obtain ⟨valid,cover,strict⟩:=original_parent_valid_cover_and_strict q T S c d proper selected picked below
 refine ⟨valid,?_⟩
 intro F agree affordable cohabit
 exact cover F agree (original_cohabit_refines_parents q T S c d proper selected picked F agree cohabit) affordable

theorem original_disjoint_run_query_exact (q : Nat) (T S : Tree) (c d : Candidate)
 (proper : DepthOne.proper T S=true) (selected : FastOrdinary.early T S=.hard2 c d)
 (picked : Hard2Overlap.runHard2 T S c=some .disjoint)
 (below : IndependentReconstruction.BelowBudget q) :
 QueryExact T S q (DisjointParents.run (IndependentReconstruction.OwnPaid q) T S c.a c.b q) := by
 obtain ⟨ht,hs,hf,hr⟩:=original_early_hard2_fields selected
 have combined:=UnitPaidCombination.original_combine_query_exact T S c q _ proper ht below
  (original_cohabiting_parent_cover q T S c d proper selected picked below)
 exact Eq.mp (congrArg (QueryExact T S q)
  (literal_disjoint_combined_answer (IndependentReconstruction.OwnPaid q) T S c.a c.b q).symm) combined

theorem original_mixed_query_exact (q : Nat) (T S : Tree) (c d : Candidate)
 (proper : DepthOne.proper T S=true) (selected : FastOrdinary.early T S=.hard2 c d)
 (picked : Hard2Overlap.runHard2 T S c=some .disjoint)
 (below : IndependentReconstruction.BelowBudget q)
 (good : (pendantPartition S c.a c.b).all (restrictionAgrees T S)=false)
 (notRule5 : ((pendantPartition S c.a c.b).filter (restrictionAgrees T S)).length≠2) :
 QueryExact T S q (Hard2Dispatcher.run (IndependentReconstruction.OwnPaid q) T S c d q) := by
 exact Eq.mp (congrArg (QueryExact T S q)
  (actual_disjoint_mixed_route (IndependentReconstruction.OwnPaid q) T S c d q picked good notRule5).symm)
  (original_disjoint_run_query_exact q T S c d proper selected picked below)

theorem original_mixed_query_exact_and_strict (q : Nat) (T S : Tree) (c d : Candidate)
 (proper : DepthOne.proper T S=true) (selected : FastOrdinary.early T S=.hard2 c d)
 (picked : Hard2Overlap.runHard2 T S c=some .disjoint)
 (below : IndependentReconstruction.BelowBudget q)
 (good : (pendantPartition S c.a c.b).all (restrictionAgrees T S)=false)
 (notRule5 : ((pendantPartition S c.a c.b).filter (restrictionAgrees T S)).length≠2) :
 QueryExact T S q (Hard2Dispatcher.run (IndependentReconstruction.OwnPaid q) T S c d q) ∧
 (Hard2Dispatcher.run (IndependentReconstruction.OwnPaid q) T S c d q=
  (Hard2Combine.combine (IndependentReconstruction.OwnPaid q) T S c.a c.b q
   (DisjointParents.query (IndependentReconstruction.OwnPaid q) T S (pendantPartition S c.a c.b) q)).answer) ∧
 ∀call∈(Hard2Combine.combine (IndependentReconstruction.OwnPaid q) T S c.a c.b q
   (DisjointParents.query (IndependentReconstruction.OwnPaid q) T S (pendantPartition S c.a c.b) q)).calls,
  call.budget<q := by
 exact ⟨original_mixed_query_exact q T S c d proper selected picked below good notRule5,
  actual_mixed_combined_route _ T S c d q picked good notRule5,
  original_mixed_combined_calls_strict q T S c d proper selected picked below⟩

/-- Actual disjoint specialization of Hard2Rule outside its separate Rule5 branch.
The Rule5 count=2 arm and all non-disjoint dispatch arms remain separate obligations. -/
theorem original_disjoint_non_rule5_hard2 (q : Nat) (T S : Tree) (c d : Candidate)
 (proper : DepthOne.proper T S=true) (pretest : DepthOne.pretest01 T S=.rejected)
 (selected : FastOrdinary.early T S=.hard2 c d)
 (picked : Hard2Overlap.runHard2 T S c=some .disjoint)
 (below : IndependentReconstruction.BelowBudget q)
 (notRule5 : ((pendantPartition S c.a c.b).filter (restrictionAgrees T S)).length≠2) :
 QueryExact T S q (Hard2Dispatcher.run (IndependentReconstruction.OwnPaid q) T S c d q) := by
 cases good : (pendantPartition S c.a c.b).all (restrictionAgrees T S) with
 | false => exact original_mixed_query_exact q T S c d proper selected picked below good notRule5
 | true => exact original_all_good_query_exact q T S c d proper pretest selected picked good
end FreshLiteralDisjoint
#print axioms FreshLiteralDisjoint.original_cohabiting_parent_cover
#print axioms FreshLiteralDisjoint.original_disjoint_run_query_exact
#print axioms FreshLiteralDisjoint.original_mixed_query_exact
#print axioms FreshLiteralDisjoint.original_mixed_query_exact_and_strict
#print axioms FreshLiteralDisjoint.original_disjoint_non_rule5_hard2

-- Author integration type/axiom reports; proof text above is unchanged apart from recorded import edits.
set_option pp.universes true
#check @FreshLiteralDisjoint.original_cohabiting_parent_cover
#print axioms FreshLiteralDisjoint.original_cohabiting_parent_cover
#check @FreshLiteralDisjoint.original_disjoint_run_query_exact
#print axioms FreshLiteralDisjoint.original_disjoint_run_query_exact
#check @FreshLiteralDisjoint.original_mixed_query_exact
#print axioms FreshLiteralDisjoint.original_mixed_query_exact
#check @FreshLiteralDisjoint.original_mixed_query_exact_and_strict
#print axioms FreshLiteralDisjoint.original_mixed_query_exact_and_strict
#check @FreshLiteralDisjoint.original_disjoint_non_rule5_hard2
#print axioms FreshLiteralDisjoint.original_disjoint_non_rule5_hard2
