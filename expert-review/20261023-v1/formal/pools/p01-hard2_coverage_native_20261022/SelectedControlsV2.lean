/- Fixed controls pinned before selected-domain proof development. Contacted only. -/
import SlimSourceControlsV3
open RMAF ForestState Universal233 Universal233.HardParent Universal233.CherryBranching
open OrdinaryDispatch OrdinaryDispatch.FastOrdinary IndependentOneExchange ContactedRepair
namespace ContactedOneConsumer

def oneC : Candidate := ⟨[false,false],0,1,cuts selectedS 0 1⟩
def badC : Candidate := ⟨[false,false],0,1,[]⟩

theorem selected_one_positive_control :
 early selectedT selectedS=.one false oneC ∧
 early selectedS selectedT=.one false (Candidate.mk [false,false] 0 2 (cuts selectedT 0 2)) ∧
 CoreGraph.CherryAt selectedT oneC.parent oneC.a oneC.b ∧
 (cuts selectedS oneC.a oneC.b).length=1 ∧
 (pendantChild selectedS oneC.a oneC.b).paid=1 := by
 exact ⟨rfl,rfl,rfl,by decide,rfl⟩

theorem forged_candidate_negative_control :
 early selectedT selectedS≠.one false badC ∧
 badC.originalCuts≠cuts selectedS badC.a badC.b := by
 constructor
 · intro h
   have eq : oneC=badC := (Early.one.inj h).2
   have bad := congrArg Candidate.originalCuts eq
   change [[false,false,true]]=[] at bad
   cases bad
 · decide

theorem hostile_original_partition_control :
 partitionCheck (leaves selectedS) [[2],[2],[0,1,3,4,5]]=false ∧
 pairwiseEmbeddings selectedS [[0,1,5],[2],[3,4]]=false := by decide
end ContactedOneConsumer

-- Author integration type/axiom reports; proof text above is unchanged apart from recorded import edits.
set_option pp.universes true
#check @ContactedOneConsumer.selected_one_positive_control
#print axioms ContactedOneConsumer.selected_one_positive_control
#check @ContactedOneConsumer.forged_candidate_negative_control
#print axioms ContactedOneConsumer.forged_candidate_negative_control
#check @ContactedOneConsumer.hostile_original_partition_control
#print axioms ContactedOneConsumer.hostile_original_partition_control
