import AdmittedOrdered
namespace AdmittedRule5Author
open RMAF Universal233 Universal233.CherryBranching Universal233.Rule5Local Universal233.HardParent
open OrdinaryDispatch Universal233.Hard2Overlap

-- This is an explicit consumer premise, awaiting the separately authored
-- immutable generic zero-cut release. No realization of it is asserted here.
def CommonCherryZeroCuts : Prop := ∀ (U : Tree) (x y : Nat),
 (leaves U).Nodup → HasCherry x y U → pendantOriginal U x y=[]

theorem literal_rule4_priority (zeroCuts : CommonCherryZeroCuts)
 (T S : Tree) (proper : DepthOne.proper T S=true)
 (forward : earlierClear T S=true) (reverse : earlierClear S T=true) :
 Rule4.Priority T S := by
 have h : (decide (leaves T).Nodup=true ∧ decide (leaves S).Nodup=true) ∧ decide ((leaves T).Perm (leaves S))=true := by
  simpa only [DepthOne.proper,Bool.and_eq_true] using proper
 have hnT : (leaves T).Nodup:=of_decide_eq_true h.1.1
 have hnS : (leaves S).Nodup:=of_decide_eq_true h.1.2
 refine ⟨hnT,hnS,of_decide_eq_true h.2,?_,?_,?_⟩
 · apply List.all_eq_true.mpr
   intro p hp
   cases contained : (Rule4.orderedCherries S).contains p with
   | false => rfl
   | true =>
    have memS:=List.contains_iff_mem.mp contained
    have two:=earlier_clear_ordered_length T S forward p hp
    have zero:=zeroCuts S p.1 p.2 hnS (ordered_hasCherry S p.1 p.2 memS)
    rw [zero] at two
    cases two
 · apply List.all_eq_true.mpr
   intro p hp
   have two:=earlier_clear_ordered_length T S forward p hp
   rw [two]
   rfl
 · apply List.all_eq_true.mpr
   intro p hp
   have two:=earlier_clear_ordered_length S T reverse p hp
   rw [two]
   rfl

theorem proper_reverse (T S : Tree) (proper : DepthOne.proper T S=true) :
 DepthOne.proper S T=true := by
 have h : (decide (leaves T).Nodup=true ∧ decide (leaves S).Nodup=true) ∧ decide ((leaves T).Perm (leaves S))=true := by
  simpa only [DepthOne.proper,Bool.and_eq_true] using proper
 have hp : (leaves T).Perm (leaves S):=of_decide_eq_true h.2
 simp only [DepthOne.proper,Bool.and_eq_true]
 exact ⟨⟨h.1.2,h.1.1⟩,decide_eq_true hp.symm⟩

theorem actual_admitted (zeroCuts : CommonCherryZeroCuts)
 (T S : Tree) (c d : Candidate)
 (proper : DepthOne.proper T S=true)
 (early : FastOrdinary.early T S=.hard2 c d)
 (graph : runHard2 T S c=some .disjoint)
 (twoGood : ((pendantPartition S c.a c.b).filter (restrictionAgrees T S)).length=2) :
 admitted T S c.a c.b=true := by
 have front:=actual_front_checks T S c d proper early
 have priority:=literal_rule4_priority zeroCuts T S proper front.2.2.1 front.2.2.2.1
 have revPriority:=literal_rule4_priority zeroCuts S T (proper_reverse T S proper) front.2.2.2.1 front.2.2.1
 have noForward:=selected_rule4_none_syntactic_false T S priority front.2.2.2.2.2.1
 have noReverse:=selected_rule4_none_syntactic_false S T revPriority front.2.2.2.2.2.2
 have target:=actual_target_embeddings T S c d proper early graph
 have source:=actual_source_embeddings T S c.a c.b proper
 simp only [admitted,front.1,front.2.1,front.2.2.1,front.2.2.2.1,
  noForward,noReverse,front.2.2.2.2.1,target,source,twoGood,
  Bool.not_false,Bool.true_and,beq_self_eq_true]

theorem actual_two_good_not_all (T S : Tree) (c d : Candidate)
 (proper : DepthOne.proper T S=true)
 (early : FastOrdinary.early T S=.hard2 c d)
 (twoGood : ((pendantPartition S c.a c.b).filter (restrictionAgrees T S)).length=2) :
 (pendantPartition S c.a c.b).all (restrictionAgrees T S)=false := by
 have front:=actual_front_checks T S c d proper early
 have len : (pendantPartition S c.a c.b).length=3 := by
  simp only [pendantPartition,List.length_append,List.length_map,List.length_cons,List.length_nil]
  rw [front.2.2.2.2.1]
 cases allGood : (pendantPartition S c.a c.b).all (restrictionAgrees T S) with
 | false => rfl
 | true =>
  have allMembers:=List.all_eq_true.mp allGood
  have equal : (pendantPartition S c.a c.b).filter (restrictionAgrees T S)=pendantPartition S c.a c.b :=
   List.filter_eq_self.mpr allMembers
  rw [equal,len] at twoGood
  cases twoGood

theorem actual_rule5_route (actual : Rule5OrdinaryDispatch.Ordinary)
 (T S : Tree) (c d : Candidate) (q : Nat)
 (proper : DepthOne.proper T S=true)
 (early : FastOrdinary.early T S=.hard2 c d)
 (graph : runHard2 T S c=some .disjoint)
 (twoGood : ((pendantPartition S c.a c.b).filter (restrictionAgrees T S)).length=2) :
 Hard2Dispatcher.run actual T S c d q=Hard2Dispatcher.rule5Answer actual T S c.a c.b q :=
 literal_two_good_route actual T S c d q graph
  (actual_two_good_not_all T S c d proper early twoGood) twoGood


end AdmittedRule5Author

-- Author integration reports only: original source prefix above is unchanged.
set_option pp.universes true
#check @AdmittedRule5Author.literal_rule4_priority
#print axioms AdmittedRule5Author.literal_rule4_priority
#check @AdmittedRule5Author.proper_reverse
#print axioms AdmittedRule5Author.proper_reverse
#check @AdmittedRule5Author.actual_admitted
#print axioms AdmittedRule5Author.actual_admitted
#check @AdmittedRule5Author.actual_two_good_not_all
#print axioms AdmittedRule5Author.actual_two_good_not_all
#check @AdmittedRule5Author.actual_rule5_route
#print axioms AdmittedRule5Author.actual_rule5_route
