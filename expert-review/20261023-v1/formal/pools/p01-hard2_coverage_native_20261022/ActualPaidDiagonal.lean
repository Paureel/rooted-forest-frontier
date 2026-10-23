import DiagonalCoupling
open RMAF VertexGeometry ForestState ForestGroups RestrictionBridge Universal233 Universal233.CherryBranching
open OrdinaryDispatch OrdinaryDispatch.FastOrdinary ContactedHard2Parent ContactedHard2Overlap
namespace ContactedHard2Survival

theorem actual_diagonal_paid_cover (ordinary : PaidInstances.OrdinarySolver) (q : Nat) (T S : Tree)
 (c d : Candidate) (p r v w : RMAF.Vertex) (ord : Order) (proper : DepthOne.proper T S=true)
 (selected : early T S=.hard2 c d) (shape : c.originalCuts=[p,r])
 (picked : ContactedActualHard2.runHard2 T S c=some (.diagonal ord v w))
 (below : PaidInstances.BelowBudget ordinary q) (F : List (List Nat)) (agree : agreement T S F=true)
 (together : ∃D,D∈F ∧ c.a∈D ∧ c.b∈D) (budget : F.length-1≤q) :
 ∃G,(Hard2PaidLocal.runHardPaid (PaidInstances.OwnPaid ordinary q) T S q c (.diagonal (originalOrder ord) v w)).answer=some G ∧
 agreement T S G=true ∧ G.length≤F.length := by
 have scope:=actual_competitor_scope T S c d p r proper selected shape ord F agree together
 have valid:=actual_picked_valid T S c d p r proper selected shape (.diagonal ord v w) picked
 apply actual_source_survivor_paid ordinary q T S c d p r proper selected shape below F agree budget (.diagonal ord v w)
 exact diagonal_source_cover T S _ _ _ q F v w proper scope.1 agree scope.2.2.1 budget
  valid.1.1 valid.1.2.1 valid.1.2.2.2.1 valid.1.2.2.2.2.1 valid.2
end ContactedHard2Survival

-- Author integration type/axiom reports; proof text above is unchanged apart from recorded import edits.
set_option pp.universes true
#check @ContactedHard2Survival.actual_diagonal_paid_cover
#print axioms ContactedHard2Survival.actual_diagonal_paid_cover
