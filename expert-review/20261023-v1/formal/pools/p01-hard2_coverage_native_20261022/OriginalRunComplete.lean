import OriginalPaidComplete
import UnitOriginal02
open RMAF Universal233 Universal233.CherryBranching OrdinaryDispatch OrdinaryDispatch.FastOrdinary
set_option autoImplicit false
namespace ContactedHard2Survival

theorem original_paid_cover_record (q : Nat) (T S : Tree) (c d : Candidate)
 (proper : DepthOne.proper T S=true) (rejected : DepthOne.pretest01 T S=.rejected)
 (selected : early T S=.hard2 c d) (out : Hard2Overlap.Result)
 (picked : Hard2Overlap.runHard2 T S c=some out) (nonDisjoint : out≠.disjoint)
 (below : IndependentReconstruction.BelowBudget q) :
 UnitPaidCombination.CohabitingPaidCover T S c q (Hard2Dispatcher.paidCase (IndependentReconstruction.OwnPaid q) T S c q out) := by
 refine ⟨?_,?_⟩
 · intro G found
   exact original_paidCase_sound (IndependentReconstruction.OwnPaid q) T S c d proper selected out q G found
 · intro F agree budget together
   obtain ⟨G,found,_,least⟩:=original_paid_cohabit_cover q T S c d proper rejected selected out picked nonDisjoint below F agree together budget
   exact ⟨G,found,least⟩

theorem original_nondisjoint_run_query_exact (q : Nat) (T S : Tree) (c d : Candidate)
 (proper : DepthOne.proper T S=true) (rejected : DepthOne.pretest01 T S=.rejected)
 (selected : early T S=.hard2 c d) (out : Hard2Overlap.Result)
 (picked : Hard2Overlap.runHard2 T S c=some out) (nonDisjoint : out≠.disjoint)
 (below : IndependentReconstruction.BelowBudget q) :
 QueryExact T S q (Hard2Dispatcher.run (IndependentReconstruction.OwnPaid q) T S c d q) := by
 have paidCover:=original_paid_cover_record q T S c d proper rejected selected out picked nonDisjoint below
 have selection:=(ContactedHard2.early_hard2_saved selected).1
 have combined:=UnitPaidCombination.original_combine_query_exact T S c q _ proper selection below paidCover
 have route : Hard2Dispatcher.run (IndependentReconstruction.OwnPaid q) T S c d q=
  (Hard2Combine.combine (IndependentReconstruction.OwnPaid q) T S c.a c.b q
    (Hard2Dispatcher.paidCase (IndependentReconstruction.OwnPaid q) T S c q out)).answer := by
  unfold Hard2Dispatcher.run
  rw [picked]
  cases out with
  | disjoint=>exact False.elim (nonDisjoint rfl)
  | clique v=>rfl
  | four ord v w=>rfl
  | diagonal ord v w=>rfl
  | pair ord ch=>rfl
 rw [route]
 exact combined

-- Exact remaining consuming premise. No unrestricted mixed disjoint QueryExact
-- is inferred from saved all-good or parent-refining contracts.
def OriginalDisjointRunRule : Prop :=
 ∀q T S c d,DepthOne.proper T S=true→DepthOne.pretest01 T S=.rejected→early T S=.hard2 c d→
 IndependentReconstruction.BelowBudget q→Hard2Overlap.runHard2 T S c=some .disjoint→
 QueryExact T S q (Hard2Dispatcher.run (IndependentReconstruction.OwnPaid q) T S c d q)

theorem original_hard2_rule_of_disjoint (disjoint : OriginalDisjointRunRule) : IndependentReconstruction.Hard2Rule := by
 intro q T S c d proper rejected selected below
 obtain ⟨out,ownPicked⟩:=ContactedActualHard2.runHard2_total proper selected
 have picked : Hard2Overlap.runHard2 T S c=some (originalResult out):=by
  rw [actual_runHard2_original,ownPicked]
  rfl
 by_cases apart : originalResult out=.disjoint
 · rw [apart] at picked
   exact disjoint q T S c d proper rejected selected below picked
 · exact original_nondisjoint_run_query_exact q T S c d proper rejected selected (originalResult out) picked apart below
end ContactedHard2Survival

-- Author integration type/axiom reports; proof text above is unchanged apart from recorded import edits.
set_option pp.universes true
#check @ContactedHard2Survival.original_paid_cover_record
#print axioms ContactedHard2Survival.original_paid_cover_record
#check @ContactedHard2Survival.original_nondisjoint_run_query_exact
#print axioms ContactedHard2Survival.original_nondisjoint_run_query_exact
#check @ContactedHard2Survival.original_hard2_rule_of_disjoint
#print axioms ContactedHard2Survival.original_hard2_rule_of_disjoint
