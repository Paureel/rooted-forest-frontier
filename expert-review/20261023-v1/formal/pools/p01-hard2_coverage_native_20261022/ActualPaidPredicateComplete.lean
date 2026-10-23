import ActualGoodEdgePaid
open RMAF VertexGeometry ForestState ForestGroups RestrictionBridge Universal233 Universal233.CherryBranching
open OrdinaryDispatch OrdinaryDispatch.FastOrdinary ContactedHard2Parent ContactedHard2Overlap
namespace ContactedHard2Survival

theorem original_actualPaidCase_complete (ordinary : PaidInstances.OrdinarySolver) (q : Nat) (T S : Tree)
 (c d : Candidate) (proper : DepthOne.proper T S=true) (selected : early T S=.hard2 c d)
 (out : Hard2Overlap.Result) (picked : Hard2Overlap.runHard2 T S c=some out)
 (paid : Hard2PaidLocal.actualPaidCase S T c out)
 (below : PaidInstances.BelowBudget ordinary q) (F : List (List Nat)) (agree : agreement T S F=true)
 (together : ∃D,D∈F ∧ c.a∈D ∧ c.b∈D) (budget : F.length-1≤q) :
 ∃G,(Hard2PaidLocal.runHardPaid (PaidInstances.OwnPaid ordinary q) T S q c out).answer=some G ∧
 agreement T S G=true ∧ G.length≤F.length := by
 by_cases simple : FourPaidCases out
 · exact original_four_paid_cases_cover ordinary q T S c d proper selected out picked simple below F agree together budget
 · obtain ⟨p,r,shape⟩:=ContactedActualHard2.actual_two_cuts proper selected
   have ownPicked : ContactedActualHard2.runHard2 T S c=some (contactedResult out) :=
    original_selector_picked T S c (contactedResult out) (by rw [contacted_original_inverse];exact picked)
   cases out with
   | disjoint=>simp only [Hard2PaidLocal.actualPaidCase,shape,Hard2PaidLocal.PaidCase] at paid
   | clique v=>exact False.elim (simple True.intro)
   | four ord v w=>exact False.elim (simple True.intro)
   | diagonal ord v w=>exact False.elim (simple True.intro)
   | pair ord choice=>
    cases choice with
    | vertex v=>exact False.elim (simple True.intro)
    | edge e=>
     have ori : originalOrder (contactedOrder ord)=ord := by cases ord <;>rfl
     have lp : PaidAssembly.leftParent S p=leftParent S p := rfl
     have rp : PaidAssembly.rightParent S r=rightParent S r := rfl
     have cp : PaidAssembly.rootParent S p r=rootParent S p r := rfl
     have good : restrictionAgrees S T (Hard2Overlap.first ord (leftParent S p) (rightParent S r) (rootParent S p r))=true ∨
                 restrictionAgrees S T (Hard2Overlap.second ord (leftParent S p) (rightParent S r) (rootParent S p r))=true := by
      simpa only [Hard2PaidLocal.actualPaidCase,shape,Hard2PaidLocal.PaidCase,lp,rp,cp] using paid
     rw [←ori,first_original,second_original] at good
     have result:=actual_good_edge_paid_cover ordinary q T S c d p r (contactedOrder ord) e proper selected shape
      ownPicked good below F agree together budget
     rw [ori] at result
     exact result
end ContactedHard2Survival

-- Author integration type/axiom reports; proof text above is unchanged apart from recorded import edits.
set_option pp.universes true
#check @ContactedHard2Survival.original_actualPaidCase_complete
#print axioms ContactedHard2Survival.original_actualPaidCase_complete
