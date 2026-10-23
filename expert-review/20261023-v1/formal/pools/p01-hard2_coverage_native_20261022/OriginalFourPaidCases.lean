import OriginalSelectorTransport
open RMAF VertexGeometry ForestState ForestGroups RestrictionBridge Universal233 Universal233.CherryBranching
open OrdinaryDispatch OrdinaryDispatch.FastOrdinary ContactedHard2Parent ContactedHard2Overlap
namespace ContactedHard2Survival

def FourPaidCases : Hard2Overlap.Result→Prop
 | .clique _=>True
 | .four _ _ _=>True
 | .diagonal _ _ _=>True
 | .pair _ (.vertex _)=>True
 | _=>False

theorem original_four_paid_cases_cover (ordinary : PaidInstances.OrdinarySolver) (q : Nat) (T S : Tree)
 (c d : Candidate) (proper : DepthOne.proper T S=true) (selected : early T S=.hard2 c d)
 (out : Hard2Overlap.Result) (picked : Hard2Overlap.runHard2 T S c=some out) (case : FourPaidCases out)
 (below : PaidInstances.BelowBudget ordinary q) (F : List (List Nat)) (agree : agreement T S F=true)
 (together : ∃D,D∈F ∧ c.a∈D ∧ c.b∈D) (budget : F.length-1≤q) :
 ∃G,(Hard2PaidLocal.runHardPaid (PaidInstances.OwnPaid ordinary q) T S q c out).answer=some G ∧
 agreement T S G=true ∧ G.length≤F.length := by
 obtain ⟨p,r,shape⟩:=ContactedActualHard2.actual_two_cuts proper selected
 have ownPicked : ContactedActualHard2.runHard2 T S c=some (contactedResult out) :=
  original_selector_picked T S c (contactedResult out) (by rw [contacted_original_inverse];exact picked)
 cases out with
 | disjoint=>cases case
 | clique v=>exact actual_clique_paid_cover ordinary q T S c d p r v proper selected shape ownPicked below F agree together budget
 | four ord v w=>
  have result:=actual_four_paid_cover ordinary q T S c d p r v w (contactedOrder ord) proper selected shape ownPicked below F agree together budget
  have eq : originalOrder (contactedOrder ord)=ord := by cases ord <;>rfl
  rw [eq] at result;exact result
 | diagonal ord v w=>
  have result:=actual_diagonal_paid_cover ordinary q T S c d p r v w (contactedOrder ord) proper selected shape ownPicked below F agree together budget
  have eq : originalOrder (contactedOrder ord)=ord := by cases ord <;>rfl
  rw [eq] at result;exact result
 | pair ord choice=>
  cases choice with
  | edge e=>cases case
  | vertex v=>
   have result:=actual_vertex_paid_cover ordinary q T S c d p r v (contactedOrder ord) proper selected shape ownPicked below F agree together budget
   have eq : originalOrder (contactedOrder ord)=ord := by cases ord <;>rfl
   rw [eq] at result;exact result
end ContactedHard2Survival

-- Author integration type/axiom reports; proof text above is unchanged apart from recorded import edits.
set_option pp.universes true
#check @ContactedHard2Survival.original_four_paid_cases_cover
#print axioms ContactedHard2Survival.original_four_paid_cases_cover
