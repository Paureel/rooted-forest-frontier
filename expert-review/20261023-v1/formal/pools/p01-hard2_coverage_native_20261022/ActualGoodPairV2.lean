import SelectPairIsolation
open RMAF ForestState ForestGroups RestrictionBridge Universal233 Universal233.CherryBranching
open OrdinaryDispatch OrdinaryDispatch.FastOrdinary ContactedHard2Parent ContactedForward
namespace ContactedHard2Overlap

theorem original_parents_perm (o : Order) (A B C : List Nat) :
 ([A,B,C] : List (List Nat)).Perm [first o A B C,second o A B C,third o A B C] := by
 cases o with
 | abc => exact List.Perm.refl _
 | acb => exact List.Perm.cons A (List.Perm.swap C B [])
 | bac => exact List.Perm.swap B A [C]
 | bca => exact List.perm_append_comm (l₁:=[A]) (l₂:=[B,C])
end ContactedHard2Overlap
namespace ContactedActualHard2
open ContactedHard2Overlap

def runHard2 (T S : Tree) (c : Candidate) : Option Result :=
 match c.originalCuts with
 | [p,r] => select T (leftParent S p) (rightParent S r) (rootParent S p r)
 | _ => none

theorem selected_pair_cover (ordinary : PaidInstances.OrdinarySolver) (q : Nat)
 (T S : Tree) (c d : Candidate) (p r : RMAF.Vertex)
 (proper : DepthOne.proper T S=true) (rejected : DepthOne.pretest01 T S=.rejected)
 (selected : early T S=.hard2 c d) (shape : c.originalCuts=[p,r])
 (o : Order) (choice : PairGeometry.Choice) (picked : runHard2 T S c=some (.pair o choice))
 (goodX : restrictionAgrees S T (first o (leftParent S p) (rightParent S r) (rootParent S p r))=true)
 (goodY : restrictionAgrees S T (second o (leftParent S p) (rightParent S r) (rootParent S p r))=true)
 (below : PaidInstances.BelowBudget ordinary q)
 (F : List (List Nat)) (agree : agreement T S F=true)
 (together : ∃D,D∈F ∧ c.a∈D ∧ c.b∈D) (budget : F.length-1≤q) :
 let X:=first o (leftParent S p) (rightParent S r) (rootParent S p r)
 let Y:=second o (leftParent S p) (rightParent S r) (rootParent S p r)
 let Z:=third o (leftParent S p) (rightParent S r) (rootParent S p r)
 ∃G,(ContactedGoodPair.runPair (PaidInstances.OwnPaid ordinary q) T S X Y Z q).answer=some G ∧
 agreement T S G=true ∧ G.length≤F.length := by
 have perm:=original_parents_perm o (leftParent S p) (rightParent S r) (rootParent S p r)
 have checks:=ContactedHard2Parent.actual_permuted_source_checks proper selected shape _ _ _ perm
 have selectPair : select T (leftParent S p) (rightParent S r) (rootParent S p r)=some (.pair o choice) := by
  simpa only [runHard2,shape] using picked
 have clear:=select_pair_isolation _ _ _ _ _ _ selectPair
 have domain:=ContactedHard2.actual_hard2_domain proper selected
 have ref:=ContactedForward.cohabit_refines_address proper domain.2.1.1 agree together
 rw [literal_pendant_eq,ContactedHard2Parent.actual_parent_tuple proper selected shape] at ref
 have oriented : VertexGeometry.Refines F
  [first o (leftParent S p) (rightParent S r) (rootParent S p r),
   second o (leftParent S p) (rightParent S r) (rootParent S p r),
   third o (leftParent S p) (rightParent S r) (rootParent S p r)] := by
  intro D member
  obtain ⟨U,hU,sub⟩:=ref D member
  exact ⟨U,perm.mem_iff.1 hU,sub⟩
 obtain ⟨G,runG,agreeG,_,least⟩:=ContactedGoodPair.pair_complete_isolated ordinary q T S _ _ _
  proper checks.1 checks.2 clear.1 clear.2 goodX goodY below F agree oriented budget
 exact ⟨G,runG,agreeG,least⟩
end ContactedActualHard2

-- Author integration type/axiom reports; proof text above is unchanged apart from recorded import edits.
set_option pp.universes true
#check @ContactedHard2Overlap.original_parents_perm
#print axioms ContactedHard2Overlap.original_parents_perm
#check @ContactedActualHard2.selected_pair_cover
#print axioms ContactedActualHard2.selected_pair_cover
