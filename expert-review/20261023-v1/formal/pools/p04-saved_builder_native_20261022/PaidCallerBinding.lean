import PaidBuilderRealization
namespace PaidBuilderAuthor
open RMAF Universal233 Universal233.CherryBranching Universal233.Rule5Local
open Universal233.CoreGraph Universal233.HardParent
open Universal233.Rule5Classification Universal233.Rule5FinalClassification OrdinaryDispatch
open Universal233.Hard2Overlap AdmittedRule5Author
open Universal233.Case322Extraction Universal233.Rule5PaidSelector
open Universal233.Rule5SourceOrientation

theorem actual_final_available (T S : Tree) (c d : Candidate)
 (proper:DepthOne.proper T S=true) (pretest:DepthOne.pretest01 T S=.rejected)
 (early:FastOrdinary.early T S=.hard2 c d) (graph:runHard2 T S c=some .disjoint)
 (two:((pendantPartition S c.a c.b).filter (restrictionAgrees T S)).length=2) :
 ∃z,selectFinal T S c.a c.b=some z := by
 apply admitted_final_available T S c.a c.b (actual_admitted_closed T S c d proper early graph two)
 intro remaining
 exact remaining_source_contract T S c d proper pretest early graph two remaining

theorem actual_second_build_selected (T S : Tree) (c d : Candidate) (bad : BadSelection) (u v : Vertex)
 (proper:DepthOne.proper T S=true) (early:FastOrdinary.early T S=.hard2 c d)
 (graph:runHard2 T S c=some .disjoint)
 (pick:selectFinal T S c.a c.b=some (.remaining bad (.second u v))) :
 ∃R,buildSelected T S c.a c.b=some R :=
 selected_second_built T S c.a c.b bad u v pick (actual_second_paid_builder T S c d bad u v proper early graph pick)

theorem actual_second_no_builder_refusal (actual : Rule5OrdinaryDispatch.Ordinary)
 (T S : Tree) (c d : Candidate) (bad : BadSelection) (u v : Vertex) (q : Nat)
 (proper:DepthOne.proper T S=true) (early:FastOrdinary.early T S=.hard2 c d)
 (graph:runHard2 T S c=some .disjoint)
 (pick:selectFinal T S c.a c.b=some (.remaining bad (.second u v))) :
 Rule5OrdinaryDispatch.dispatch actual T S c.a c.b q≠.paidBuilderRefused :=
 selected_second_no_refusal actual T S c.a c.b q bad u v pick
  (actual_second_paid_builder T S c d bad u v proper early graph pick)

theorem actual_rule5_operational_answer (actual : Rule5OrdinaryDispatch.Ordinary)
 (T S : Tree) (c d : Candidate) (q : Nat)
 (proper:DepthOne.proper T S=true) (pretest:DepthOne.pretest01 T S=.rejected)
 (early:FastOrdinary.early T S=.hard2 c d) (graph:runHard2 T S c=some .disjoint)
 (two:((pendantPartition S c.a c.b).filter (restrictionAgrees T S)).length=2) :
 ∃answer,Rule5OrdinaryDispatch.dispatch actual T S c.a c.b q=.answered answer := by
 obtain ⟨z,pick⟩:=actual_final_available T S c d proper pretest early graph two
 cases z with
 | «prefix» s =>
  rw [Rule5OrdinaryDispatch.dispatch,pick]
  exact ⟨Rule5OrdinaryDispatch.runChildren actual T S q (localChildren S c.a c.b s),rfl⟩
 | remaining bad boundary =>
  cases boundary with
  | one w =>
   rw [Rule5OrdinaryDispatch.dispatch,pick]
   exact ⟨Rule5CommonOrdinary.runSelectedCommon actual T S c.a c.b bad q,rfl⟩
  | first u v =>
   rw [Rule5OrdinaryDispatch.dispatch,pick]
   exact ⟨Rule5OrdinaryDispatch.runChildren actual T S q (firstChildren S c.a c.b bad),rfl⟩
  | third u v =>
   rw [Rule5OrdinaryDispatch.dispatch,pick]
   exact ⟨Rule5OrdinaryDispatch.runChildren actual T S q (thirdChildren S c.a c.b bad),rfl⟩
  | second u v =>
   obtain ⟨R,built⟩:=actual_second_build_selected T S c d bad u v proper early graph pick
   simp only [Rule5OrdinaryDispatch.dispatch,pick,Rule5OrdinaryDispatch.runSelected,Rule5PaidOrdinary.solveSelected,built]
   exact ⟨_,rfl⟩

theorem actual_hard2_operational_answer (actual : Rule5OrdinaryDispatch.Ordinary)
 (T S : Tree) (c d : Candidate) (q : Nat)
 (proper:DepthOne.proper T S=true) (pretest:DepthOne.pretest01 T S=.rejected)
 (early:FastOrdinary.early T S=.hard2 c d) (graph:runHard2 T S c=some .disjoint)
 (two:((pendantPartition S c.a c.b).filter (restrictionAgrees T S)).length=2) :
 ∃answer,Rule5OrdinaryDispatch.dispatch actual T S c.a c.b q=.answered answer ∧
  Hard2Dispatcher.run actual T S c d q=answer := by
 obtain ⟨answer,dispatch⟩:=actual_rule5_operational_answer actual T S c d q proper pretest early graph two
 refine ⟨answer,dispatch,?_⟩
 rw [actual_rule5_route actual T S c d q proper early graph two,Hard2Dispatcher.rule5Answer,dispatch]

end PaidBuilderAuthor

-- Author integration reports only: original source prefix above is unchanged.
set_option pp.universes true
#check @PaidBuilderAuthor.actual_final_available
#print axioms PaidBuilderAuthor.actual_final_available
#check @PaidBuilderAuthor.actual_second_build_selected
#print axioms PaidBuilderAuthor.actual_second_build_selected
#check @PaidBuilderAuthor.actual_second_no_builder_refusal
#print axioms PaidBuilderAuthor.actual_second_no_builder_refusal
#check @PaidBuilderAuthor.actual_rule5_operational_answer
#print axioms PaidBuilderAuthor.actual_rule5_operational_answer
#check @PaidBuilderAuthor.actual_hard2_operational_answer
#print axioms PaidBuilderAuthor.actual_hard2_operational_answer
