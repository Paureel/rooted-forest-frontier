import GoodEdgeExchange
open RMAF VertexGeometry ForestState ForestGroups RestrictionBridge Universal233 Universal233.CoreProgram Universal233.CherryBranching
open OrdinaryDispatch OrdinaryDispatch.FastOrdinary ContactedHard2Parent ContactedHard2Overlap
namespace ContactedHard2Survival

theorem actual_good_edge_paid_cover (ordinary : PaidInstances.OrdinarySolver) (q : Nat) (T S : Tree)
 (c d : Candidate) (p r : RMAF.Vertex) (ord : Order) (e : RMAF.Vertex×RMAF.Vertex)
 (proper : DepthOne.proper T S=true) (selected : early T S=.hard2 c d) (shape : c.originalCuts=[p,r])
 (picked : ContactedActualHard2.runHard2 T S c=some (.pair ord (.edge e)))
 (good : restrictionAgrees S T (first ord (leftParent S p) (rightParent S r) (rootParent S p r))=true ∨
         restrictionAgrees S T (second ord (leftParent S p) (rightParent S r) (rootParent S p r))=true)
 (below : PaidInstances.BelowBudget ordinary q) (F : List (List Nat)) (agree : agreement T S F=true)
 (together : ∃D,D∈F ∧ c.a∈D ∧ c.b∈D) (budget : F.length-1≤q) :
 ∃G,(Hard2PaidLocal.runHardPaid (PaidInstances.OwnPaid ordinary q) T S q c (.pair (originalOrder ord) (.edge e))).answer=some G ∧
 agreement T S G=true ∧ G.length≤F.length := by
 let A:=leftParent S p
 let B:=rightParent S r
 let C:=rootParent S p r
 let X:=first ord A B C
 let Y:=second ord A B C
 let Z:=third ord A B C
 have scope:=actual_competitor_scope T S c d p r proper selected shape ord F agree together
 have valid:=actual_picked_valid T S c d p r proper selected shape (.pair ord (.edge e)) picked
 obtain ⟨edge,e1x,e1y,e2x,e2y,sidesX,sidesY,clear⟩:=valid.2.2.2
 by_cases goodX : restrictionAgrees S T X=true
 · obtain ⟨J,agreeJ,refJ,leastJ,monoJ⟩:=good_edge_exchange T S X Y Z e F proper scope.1 scope.2.1
    valid.1 clear edge sidesX goodX agree scope.2.2.1
   have budgetJ : J.length-1≤q := by omega
   obtain ⟨o,member,refine,real⟩:=whole_source_cover T S X Y Z q J proper scope.1 agreeJ refJ budgetJ
    (fun _=>0) (sideColor (PairGeometry.descendants T e.2)) (fun _=>0)
    (constant_monochrome J X) monoJ (constant_monochrome J Z)
   have inCase : o∈caseOutputs S T A B C q (.pair ord (.edge e)) := by
    change o∈Hard2PaidLocal.edgeOutputs S T X Y e q
    delta Hard2PaidLocal.edgeOutputs
    rw [ite_eq_left goodX]
    exact member
   obtain ⟨G,runG,agreeG,leastG⟩:=actual_source_survivor_paid ordinary q T S c d p r proper selected shape below J agreeJ budgetJ
    (.pair ord (.edge e)) ⟨o,inCase,refine,real⟩
   exact ⟨G,runG,agreeG,Nat.le_trans leastG leastJ⟩
 · have goodY : restrictionAgrees S T Y=true := by rcases good with gx|gy;exact False.elim (goodX gx);exact gy
   have perm:=original_parents_perm ord A B C
   have swap : ([X,Y,Z] : List (List Nat)).Perm [Y,X,Z]:=List.Perm.swap _ _ _
   have checks:=ContactedHard2Parent.actual_permuted_source_checks proper selected shape Y X Z (perm.trans swap)
   have refSwap : VertexGeometry.Refines F [Y,X,Z] := by
    intro K kF
    obtain ⟨D,dP,sub⟩:=scope.2.2.1 K kF
    exact ⟨D,swap.mem_iff.mp dP,sub⟩
   have clearSwap : PairGeometry.ActualClear T Y X e.2 :=⟨clear.2,clear.1⟩
   obtain ⟨J,agreeJ,refJ,leastJ,monoJ⟩:=good_edge_exchange T S Y X Z e F proper checks.1 checks.2
    valid.2.1 clearSwap edge sidesY goodY agree refSwap
   have budgetJ : J.length-1≤q := by omega
   obtain ⟨o,member,refine,real⟩:=whole_source_cover T S Y X Z q J proper checks.1 agreeJ refJ budgetJ
    (fun _=>0) (sideColor (PairGeometry.descendants T e.2)) (fun _=>0)
    (constant_monochrome J Y) monoJ (constant_monochrome J Z)
   have inCase : o∈caseOutputs S T A B C q (.pair ord (.edge e)) := by
    change o∈Hard2PaidLocal.edgeOutputs S T X Y e q
    delta Hard2PaidLocal.edgeOutputs
    rw [ite_eq_right goodX]
    exact member
   obtain ⟨G,runG,agreeG,leastG⟩:=actual_source_survivor_paid ordinary q T S c d p r proper selected shape below J agreeJ budgetJ
    (.pair ord (.edge e)) ⟨o,inCase,refine,real⟩
   exact ⟨G,runG,agreeG,Nat.le_trans leastG leastJ⟩
end ContactedHard2Survival

-- Author integration type/axiom reports; proof text above is unchanged apart from recorded import edits.
set_option pp.universes true
#check @ContactedHard2Survival.actual_good_edge_paid_cover
#print axioms ContactedHard2Survival.actual_good_edge_paid_cover
