import CaseOutputPayment
open RMAF VertexGeometry ForestState ForestGroups RestrictionBridge Universal233 Universal233.CoreProgram Universal233.CherryBranching
open OrdinaryDispatch OrdinaryDispatch.FastOrdinary ContactedHard2Parent ContactedHard2Overlap
namespace ContactedHard2Survival

theorem actual_picked_valid (T S : Tree) (c d : Candidate) (p r : RMAF.Vertex)
 (proper : DepthOne.proper T S=true) (selected : early T S=.hard2 c d)
 (shape : c.originalCuts=[p,r]) (out : Result) (picked : ContactedActualHard2.runHard2 T S c=some out) :
 Valid T (leftParent S p) (rightParent S r) (rootParent S p r) out := by
 have part:=(ContactedHard2Parent.actual_permuted_source_checks proper selected shape _ _ _ (List.Perm.refl _)).1
 have choice : select T (leftParent S p) (rightParent S r) (rootParent S p r)=some out := by
  simpa only [ContactedActualHard2.runHard2,shape] using picked
 exact select_valid T S _ _ _ proper part out choice

theorem actual_source_survivor_paid (ordinary : PaidInstances.OrdinarySolver) (q : Nat) (T S : Tree)
 (c d : Candidate) (p r : RMAF.Vertex) (proper : DepthOne.proper T S=true)
 (selected : early T S=.hard2 c d) (shape : c.originalCuts=[p,r])
 (below : PaidInstances.BelowBudget ordinary q) (F : List (List Nat)) (agree : agreement T S F=true)
 (budget : F.length-1≤q) (out : Result)
 (survivor : ∃o,o∈caseOutputs S T (leftParent S p) (rightParent S r) (rootParent S p r) q out ∧
  VertexGeometry.Refines F o.partition ∧ CutRealization.RealizedOutput S o) :
 ∃G,(Hard2PaidLocal.runHardPaid (PaidInstances.OwnPaid ordinary q) T S q c (originalResult out)).answer=some G ∧
 agreement T S G=true ∧ G.length≤F.length := by
 obtain ⟨o,member,refine,real⟩:=survivor
 have part:=(ContactedHard2Parent.actual_permuted_source_checks proper selected shape _ _ _ (List.Perm.refl _)).1
 have payment:=literal_case_payment T S _ _ _ q proper part out o member real
 obtain ⟨G,runG,agreeG,least⟩:=literal_full_execute_complete ordinary q T S below proper _ o member
  payment.1 payment.2.1 payment.2.2.1 (by have h:=payment.2.2.2;omega) F agree refine budget
 exact ⟨G,by rw [literal_runHardPaid_original (PaidInstances.OwnPaid ordinary q) T S c p r shape q out];exact runG,agreeG,least⟩

theorem actual_clique_paid_cover (ordinary : PaidInstances.OrdinarySolver) (q : Nat) (T S : Tree)
 (c d : Candidate) (p r v : RMAF.Vertex) (proper : DepthOne.proper T S=true)
 (selected : early T S=.hard2 c d) (shape : c.originalCuts=[p,r])
 (picked : ContactedActualHard2.runHard2 T S c=some (.clique v))
 (below : PaidInstances.BelowBudget ordinary q) (F : List (List Nat)) (agree : agreement T S F=true)
 (together : ∃D,D∈F ∧ c.a∈D ∧ c.b∈D) (budget : F.length-1≤q) :
 ∃G,(Hard2PaidLocal.runHardPaid (PaidInstances.OwnPaid ordinary q) T S q c (.clique v)).answer=some G ∧
 agreement T S G=true ∧ G.length≤F.length := by
 have scope:=actual_competitor_scope T S c d p r proper selected shape .abc F agree together
 have valid:=actual_picked_valid T S c d p r proper selected shape (.clique v) picked
 apply actual_source_survivor_paid ordinary q T S c d p r proper selected shape below F agree budget (.clique v)
 exact clique_source_cover T S _ _ _ q F v proper scope.1 agree scope.2.2.1 budget valid.1

theorem actual_four_paid_cover (ordinary : PaidInstances.OrdinarySolver) (q : Nat) (T S : Tree)
 (c d : Candidate) (p r v w : RMAF.Vertex) (ord : Order) (proper : DepthOne.proper T S=true)
 (selected : early T S=.hard2 c d) (shape : c.originalCuts=[p,r])
 (picked : ContactedActualHard2.runHard2 T S c=some (.four ord v w))
 (below : PaidInstances.BelowBudget ordinary q) (F : List (List Nat)) (agree : agreement T S F=true)
 (together : ∃D,D∈F ∧ c.a∈D ∧ c.b∈D) (budget : F.length-1≤q) :
 ∃G,(Hard2PaidLocal.runHardPaid (PaidInstances.OwnPaid ordinary q) T S q c (.four (originalOrder ord) v w)).answer=some G ∧
 agreement T S G=true ∧ G.length≤F.length := by
 have scope:=actual_competitor_scope T S c d p r proper selected shape ord F agree together
 have valid:=actual_picked_valid T S c d p r proper selected shape (.four ord v w) picked
 apply actual_source_survivor_paid ordinary q T S c d p r proper selected shape below F agree budget (.four ord v w)
 exact four_source_cover T S _ _ _ q F v w proper scope.1 agree scope.2.2.1 budget valid.1.1 valid.1.2.1

theorem actual_vertex_paid_cover (ordinary : PaidInstances.OrdinarySolver) (q : Nat) (T S : Tree)
 (c d : Candidate) (p r v : RMAF.Vertex) (ord : Order) (proper : DepthOne.proper T S=true)
 (selected : early T S=.hard2 c d) (shape : c.originalCuts=[p,r])
 (picked : ContactedActualHard2.runHard2 T S c=some (.pair ord (.vertex v)))
 (below : PaidInstances.BelowBudget ordinary q) (F : List (List Nat)) (agree : agreement T S F=true)
 (together : ∃D,D∈F ∧ c.a∈D ∧ c.b∈D) (budget : F.length-1≤q) :
 ∃G,(Hard2PaidLocal.runHardPaid (PaidInstances.OwnPaid ordinary q) T S q c (.pair (originalOrder ord) (.vertex v))).answer=some G ∧
 agreement T S G=true ∧ G.length≤F.length := by
 have scope:=actual_competitor_scope T S c d p r proper selected shape ord F agree together
 have valid:=actual_picked_valid T S c d p r proper selected shape (.pair ord (.vertex v)) picked
 have apart:=partition_parent_apart _ _ _ _ scope.1
 have no:=overlap_not_target_leaf T _ _ v apart.1 valid.2.2.2.1 valid.2.2.2.2.1
 apply actual_source_survivor_paid ordinary q T S c d p r proper selected shape below F agree budget (.pair ord (.vertex v))
 exact vertex_source_cover T S _ _ _ q F v proper scope.1 agree scope.2.2.1 budget no
end ContactedHard2Survival

-- Author integration type/axiom reports; proof text above is unchanged apart from recorded import edits.
set_option pp.universes true
#check @ContactedHard2Survival.actual_picked_valid
#print axioms ContactedHard2Survival.actual_picked_valid
#check @ContactedHard2Survival.actual_source_survivor_paid
#print axioms ContactedHard2Survival.actual_source_survivor_paid
#check @ContactedHard2Survival.actual_clique_paid_cover
#print axioms ContactedHard2Survival.actual_clique_paid_cover
#check @ContactedHard2Survival.actual_four_paid_cover
#print axioms ContactedHard2Survival.actual_four_paid_cover
#check @ContactedHard2Survival.actual_vertex_paid_cover
#print axioms ContactedHard2Survival.actual_vertex_paid_cover
