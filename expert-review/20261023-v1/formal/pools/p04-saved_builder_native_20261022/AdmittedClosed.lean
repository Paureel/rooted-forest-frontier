import AdmittedNextContracts
import CommonCherryZero
namespace AdmittedRule5Author
open RMAF Universal233 Universal233.CherryBranching Universal233.Rule5Local
open Universal233.HardParent OrdinaryDispatch Universal233.Hard2Overlap

theorem commonCherry_zeroCuts : CommonCherryZeroCuts := by
 intro S a b proper cherry
 exact CommonCherryZero.pendantOriginal_eq_nil proper cherry

theorem actual_rule4_priority_closed (T S : Tree) (c d : Candidate)
 (proper : DepthOne.proper T S=true)
 (early : FastOrdinary.early T S=.hard2 c d) :
 Rule4.Priority T S := by
 have front:=actual_front_checks T S c d proper early
 exact literal_rule4_priority commonCherry_zeroCuts T S proper front.2.2.1 front.2.2.2.1

theorem actual_admitted_closed (T S : Tree) (c d : Candidate)
 (proper : DepthOne.proper T S=true)
 (early : FastOrdinary.early T S=.hard2 c d)
 (graph : runHard2 T S c=some .disjoint)
 (twoGood : ((pendantPartition S c.a c.b).filter (restrictionAgrees T S)).length=2) :
 admitted T S c.a c.b=true :=
 actual_admitted commonCherry_zeroCuts T S c d proper early graph twoGood

theorem actual_graph_disjoint_rule5_call (actual : Rule5OrdinaryDispatch.Ordinary)
 (T S : Tree) (c d : Candidate) (q : Nat)
 (proper : DepthOne.proper T S=true)
 (_pretest : DepthOne.pretest01 T S=.rejected)
 (early : FastOrdinary.early T S=.hard2 c d)
 (graph : runHard2 T S c=some .disjoint)
 (twoGood : ((pendantPartition S c.a c.b).filter (restrictionAgrees T S)).length=2) :
 admitted T S c.a c.b=true ∧
 Hard2Dispatcher.run actual T S c d q=Hard2Dispatcher.rule5Answer actual T S c.a c.b q :=
 ⟨actual_admitted_closed T S c d proper early graph twoGood,
  actual_rule5_route actual T S c d q proper early graph twoGood⟩

end AdmittedRule5Author

-- Author integration reports only: original source prefix above is unchanged.
set_option pp.universes true
#check @AdmittedRule5Author.commonCherry_zeroCuts
#print axioms AdmittedRule5Author.commonCherry_zeroCuts
#check @AdmittedRule5Author.actual_rule4_priority_closed
#print axioms AdmittedRule5Author.actual_rule4_priority_closed
#check @AdmittedRule5Author.actual_admitted_closed
#print axioms AdmittedRule5Author.actual_admitted_closed
#check @AdmittedRule5Author.actual_graph_disjoint_rule5_call
#print axioms AdmittedRule5Author.actual_graph_disjoint_rule5_call
