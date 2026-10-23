import AdmittedRule4Witness
namespace AdmittedRule5Author
open RMAF Universal233 Universal233.CherryBranching Universal233.Rule5Local Universal233.Hard2Overlap
open Universal233.Rule5FinalClassification Universal233.Rule5PaidSelector

theorem literal_two_good_route (actual : Rule5OrdinaryDispatch.Ordinary) (T S : Tree)
 (c d : Candidate) (q : Nat) (graph : runHard2 T S c=some .disjoint)
 (notAll : (pendantPartition S c.a c.b).all (restrictionAgrees T S)=false)
 (two : ((pendantPartition S c.a c.b).filter (restrictionAgrees T S)).length=2) :
 OrdinaryDispatch.Hard2Dispatcher.run actual T S c d q=
 OrdinaryDispatch.Hard2Dispatcher.rule5Answer actual T S c.a c.b q := by
 simp only [OrdinaryDispatch.Hard2Dispatcher.run,graph,notAll,Bool.false_eq_true,ite_false,two,ite_true]

theorem selected_second_refusal_iff (actual : Rule5OrdinaryDispatch.Ordinary) (T S : Tree)
 (a b q : Nat) (d : BadSelection) (u v : RMAF.Vertex)
 (selected : selectFinal T S a b=some (.remaining d (.second u v))) :
 Rule5OrdinaryDispatch.dispatch actual T S a b q=.paidBuilderRefused ↔ buildSelected T S a b=none := by
 simp only [Rule5OrdinaryDispatch.dispatch,selected,Rule5OrdinaryDispatch.runSelected,Rule5PaidOrdinary.solveSelected]
 cases built:buildSelected T S a b with
 | none => constructor <;> intro h <;> rfl
 | some R => constructor <;> intro h <;> cases h

theorem literal_selector_refusal (actual : Rule5OrdinaryDispatch.Ordinary) (T S : Tree)
 (a b q : Nat) (missing : selectFinal T S a b=none) :
 Rule5OrdinaryDispatch.dispatch actual T S a b q=.selectorRefused := by
 rw [Rule5OrdinaryDispatch.dispatch,missing]

theorem refused_rule5_answer (actual : Rule5OrdinaryDispatch.Ordinary) (T S : Tree)
 (a b q : Nat) (refused : Rule5OrdinaryDispatch.dispatch actual T S a b q=.paidBuilderRefused ∨
  Rule5OrdinaryDispatch.dispatch actual T S a b q=.selectorRefused) :
 OrdinaryDispatch.Hard2Dispatcher.rule5Answer actual T S a b q=none := by
 rcases refused with hp|hs
 · rw [OrdinaryDispatch.Hard2Dispatcher.rule5Answer,hp]
 · rw [OrdinaryDispatch.Hard2Dispatcher.rule5Answer,hs]
end AdmittedRule5Author

-- Author integration reports only: original source prefix above is unchanged.
set_option pp.universes true
#check @AdmittedRule5Author.literal_two_good_route
#print axioms AdmittedRule5Author.literal_two_good_route
#check @AdmittedRule5Author.selected_second_refusal_iff
#print axioms AdmittedRule5Author.selected_second_refusal_iff
#check @AdmittedRule5Author.literal_selector_refusal
#print axioms AdmittedRule5Author.literal_selector_refusal
#check @AdmittedRule5Author.refused_rule5_answer
#print axioms AdmittedRule5Author.refused_rule5_answer
