/- Fixed actual selected-domain control, not a solver census or exchange proof. -/
import SplitPartition
open RMAF ForestState Universal233 Universal233.HardParent Universal233.CherryBranching
open OrdinaryDispatch OrdinaryDispatch.FastOrdinary
namespace IndependentOneExchange

def selectedT : Tree := .node (.node (.node (.leaf 0) (.leaf 1)) (.leaf 2))
 (.node (.node (.leaf 3) (.leaf 4)) (.leaf 5))
def selectedS : Tree := .node (.node (.node (.leaf 0) (.leaf 2)) (.leaf 1))
 (.node (.node (.leaf 3) (.leaf 5)) (.leaf 4))
def selectedC : Candidate := ⟨[false,false],0,1,cuts selectedS 0 1⟩
def selectedF : List (List Nat) := [[0,2,3,4],[1],[5]]
def selectedH : List (List Nat) := [[0,1,3,4],[2],[5]]

theorem selected_proper : DepthOne.proper selectedT selectedS=true := by decide
 theorem selected_rejected : DepthOne.pretest01 selectedT selectedS=.rejected := by rfl
 theorem selected_early : early selectedT selectedS=.one false selectedC := by rfl
 theorem selected_cherry : CoreGraph.CherryAt selectedT selectedC.parent 0 1 := by rfl
 theorem selected_one : (cuts selectedS 0 1).length=1 := by decide
 theorem selected_control_forests :
 agreement selectedT selectedS selectedF=true ∧
 IndependentPaid.refinesCheck selectedF (pendantChild selectedS 0 1).partition=false ∧
 agreement selectedT selectedS selectedH=true ∧
 IndependentPaid.refinesCheck selectedH (pendantChild selectedS 0 1).partition=true ∧
 selectedF.length=3 ∧ selectedH.length=3 := by decide

theorem selected_original_still_needs_exchange :
 ¬feasible selectedT selectedS (pendantChild selectedS 0 1) selectedF := by
 intro hf
 have yes := (IndependentPaid.refinesCheck_iff _ _).2 hf.2
 rw [selected_control_forests.2.1] at yes
 contradiction

theorem selected_domain_has_witness :
 ∃H,feasible selectedT selectedS (pendantChild selectedS 0 1) H ∧ H.length≤selectedF.length := by
 refine ⟨selectedH,⟨selected_control_forests.2.2.1,?_⟩,Nat.le_refl _⟩
 exact (IndependentPaid.refinesCheck_iff _ _).1 selected_control_forests.2.2.2.1

theorem common_merge_control :
 let T := Tree.node (.node (.leaf 0) (.leaf 1)) (.leaf 2)
 let S := Tree.node (.leaf 2) (.node (.leaf 1) (.leaf 0))
 agreement T S [[0,2],[1]]=true ∧ mergeCommon 0 1 3 [[0,2],[1]]=[[0,1,2]] ∧
 agreement T S (mergeCommon 0 1 3 [[0,2],[1]])=true := by decide

theorem singleton_hypothesis_needed :
 (mergeCommon 0 1 3 [[0,1,2]]).length+1> ([[0,1,2]] : List (List Nat)).length := by decide

theorem source_disjointness_needed :
 (splitForest [0,1] [[0,2],[1,3]]).length> ([[0,2],[1,3]] : List (List Nat)).length+1 := by decide

theorem boundary_control :
 let T := Tree.node (.node (.leaf 0) (.leaf 1)) (.node (.leaf 2) (.leaf 3))
 ([] : Vertex)∈minimalVertices [0,2] T ∧
 splitForest [0,1] [[0,2],[1],[3]]=[[0],[2],[1],[3]] ∧
 partitionCheck [0,1,2,3] (splitForest [0,1] [[0,2],[1],[3]])=true := by decide
end IndependentOneExchange
