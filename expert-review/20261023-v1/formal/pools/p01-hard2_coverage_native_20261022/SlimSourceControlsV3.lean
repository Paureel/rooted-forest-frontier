import SelectedExchangeAssemblyV3
open RMAF ForestState Universal233 Universal233.HardParent Universal233.CherryBranching
open IndependentGeometry IndependentOneExchange ContactedClade ContactedRepair
namespace IndependentPaid
def refinesCheck (F Q : List (List Nat)) : Bool :=
 F.all (fun B=>Q.any (fun U=>B.all (fun x=>U.contains x)))
end IndependentPaid
namespace IndependentOneExchange
def selectedT : Tree := .node (.node (.node (.leaf 0) (.leaf 1)) (.leaf 2))
 (.node (.node (.leaf 3) (.leaf 4)) (.leaf 5))
def selectedS : Tree := .node (.node (.node (.leaf 0) (.leaf 2)) (.leaf 1))
 (.node (.node (.leaf 3) (.leaf 5)) (.leaf 4))
def selectedF : List (List Nat) := [[0,2,3,4],[1],[5]]
end IndependentOneExchange
namespace ContactedSource

def corruptSourceH : List (List Nat) := [[0,1,5],[2],[3,4]]

theorem original_domain_control :
 DepthOne.proper selectedT selectedS=true ∧
 cuts selectedS 0 1=[[false,false,true]] ∧
 agreement selectedT selectedS selectedF=true := by decide

theorem actual_candidate_source_control :
 (repairCandidate 0 1 6 [2] selectedF).all (restrictionAgrees selectedT selectedS)=true ∧
 pairwiseEmbeddings selectedS (repairCandidate 0 1 6 [2] selectedF)=true := by decide

theorem corrupt_source_hull_control :
 agreement selectedT selectedT corruptSourceH=true ∧
 partitionCheck (leaves selectedS) corruptSourceH=true ∧
 corruptSourceH.all (restrictionAgrees selectedT selectedS)=true ∧
 IndependentPaid.refinesCheck corruptSourceH (pendantPartition selectedS 0 1)=true ∧
 pairwiseEmbeddings selectedS corruptSourceH=false := by decide
end ContactedSource

-- Author integration type/axiom reports; proof text above is unchanged apart from recorded import edits.
set_option pp.universes true
#check @ContactedSource.original_domain_control
#print axioms ContactedSource.original_domain_control
#check @ContactedSource.actual_candidate_source_control
#print axioms ContactedSource.actual_candidate_source_control
#check @ContactedSource.corrupt_source_hull_control
#print axioms ContactedSource.corrupt_source_hull_control
