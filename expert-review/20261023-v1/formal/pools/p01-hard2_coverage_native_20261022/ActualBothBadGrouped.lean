import BothBadGroupedCover
import ActualGoodEdgePaid
import OriginalSelectorTransport
open RMAF VertexGeometry ForestState ForestGroups RestrictionBridge Universal233 Universal233.CoreProgram Universal233.CherryBranching
open OrdinaryDispatch OrdinaryDispatch.FastOrdinary ContactedHard2Parent ContactedHard2Overlap
namespace ContactedHard2Survival

theorem actual_bothbad_grouped_cover (ordinary : PaidInstances.OrdinarySolver) (q : Nat) (T S : Tree)
 (c d : Candidate) (p r : RMAF.Vertex) (ord : Order) (e : RMAF.Vertex×RMAF.Vertex)
 (proper : DepthOne.proper T S=true) (selected : early T S=.hard2 c d) (shape : c.originalCuts=[p,r])
 (picked : Hard2Overlap.runHard2 T S c=some (originalResult (.pair ord (.edge e))))
 (below : PaidInstances.BelowBudget ordinary q) (F : List (List Nat)) (agree : agreement T S F=true)
 (together : ∃D,D∈F ∧ c.a∈D ∧ c.b∈D) (budget : F.length-1≤q) :
 ∃G,(BothBadGrouped.executePair (PaidInstances.OwnPaid ordinary q) T S
  (first ord (leftParent S p) (rightParent S r) (rootParent S p r))
  (second ord (leftParent S p) (rightParent S r) (rootParent S p r))
  (third ord (leftParent S p) (rightParent S r) (rootParent S p r)) e q).answer=some G ∧
 agreement T S G=true ∧ G.length≤F.length := by
 have ownPicked:=original_selector_picked T S c (.pair ord (.edge e)) picked
 let A:=leftParent S p
 let B:=rightParent S r
 let C:=rootParent S p r
 let X:=first ord A B C
 let Y:=second ord A B C
 let Z:=third ord A B C
 have scope:=actual_competitor_scope T S c d p r proper selected shape ord F agree together
 have valid:=actual_picked_valid T S c d p r proper selected shape (.pair ord (.edge e)) ownPicked
 have perm:=original_parents_perm ord A B C
 have swap : ([X,Y,Z] : List (List Nat)).Perm [Y,X,Z]:=List.Perm.swap _ _ _
 have checks:=ContactedHard2Parent.actual_permuted_source_checks proper selected shape Y X Z (perm.trans swap)
 exact bothbad_grouped_cover ordinary q T S X Y Z e below proper scope.1 checks.1 valid.1 valid.2.1
  valid.2.2.2.1 F agree scope.2.2.1 budget
end ContactedHard2Survival

-- Author integration type/axiom reports; proof text above is unchanged apart from recorded import edits.
set_option pp.universes true
#check @ContactedHard2Survival.actual_bothbad_grouped_cover
#print axioms ContactedHard2Survival.actual_bothbad_grouped_cover
