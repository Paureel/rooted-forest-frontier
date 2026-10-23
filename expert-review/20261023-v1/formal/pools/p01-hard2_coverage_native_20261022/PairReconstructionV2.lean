-- Exact checked-output reconstruction, using only already licensed generic/DP closure.
import PairControlsV2
open RMAF ForestState ForestGroups RestrictionBridge Universal233
namespace ContactedGoodPair

theorem pair_global_reconstruction (T S : Tree) (A B C : List Nat)
 (proper : DepthOne.proper T S=true) (part : partitionCheck (leaves S) [A,B,C]=true)
 (emb : pairwiseEmbeddings S [A,B,C]=true)
 (cross : CrossClear (some T) (OutputState.sourceForest S [A,B,C]) [A++B,C])
 (H K : Forest)
 (ha : agrees (localTarget (some T) (A++B)) (owned (OutputState.sourceForest S [A,B,C]) (A++B)) H=true)
 (hb : agrees (localTarget (some T) C) (owned (OutputState.sourceForest S [A,B,C]) C) K=true) :
 agreement T S (H++K)=true ∧ VertexGeometry.Refines (H++K) [A,B,C] := by
 have scope:=ContactedHard2DP.pair_source_scope T S A B C proper part emb
 have nd:=checked_family_nodup _ _ scope.2.1
 have ne : A++B≠C := by
  simpa only [List.mem_cons,List.not_mem_nil,or_false] using (List.nodup_cons.mp nd).1
 let G := fun U : List Nat=>if U=A++B then H else K
 have localG : ∀U,U∈[A++B,C]→agrees (localTarget (some T) U)
   (owned (OutputState.sourceForest S [A,B,C]) U) (G U)=true := by
  intro U hU
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hU
  rcases hU with e|e <;> subst U
  · simpa only [G,if_pos rfl] using ha
  · simpa only [G,if_neg ne.symm] using hb
 have total:=ForestGroups.reverse_reconstruction (some T) (OutputState.sourceForest S [A,B,C])
  [A++B,C] G scope.1 scope.2.1 scope.2.2.1 cross localG
 have literal : List.flatMap G [A++B,C]=H++K := by simp only [List.flatMap_cons,List.flatMap_nil,G,if_pos rfl,if_neg ne.symm,ite_true,List.append_nil]
 rw [literal] at total
 exact (FreshResidual.residual_transfer_scope.1 T S [A,B,C] (H++K) proper part emb).2.2.1 total

theorem checked_sound {T S : Tree} {q : Nat} {o : Option Forest} {F : Forest}
 (h : checked T S q o=some F) : agreement T S F=true ∧ F.length-1≤q := by
 cases o with
 | none => simp [checked] at h
 | some G =>
  by_cases good : accept T S q G=true
  · have eq : G=F := by simpa [checked,good] using h
    subst G
    simpa only [accept,Bool.and_eq_true,decide_eq_true_eq] using good
  · simp [checked,good] at h

theorem pair_complete (ordinary : PaidInstances.OrdinarySolver) (q : Nat)
 (T S : Tree) (A B C : List Nat)
 (proper : DepthOne.proper T S=true) (part : partitionCheck (leaves S) [A,B,C]=true)
 (emb : pairwiseEmbeddings S [A,B,C]=true)
 (cross : CrossClear (some T) (OutputState.sourceForest S [A,B,C]) [A++B,C])
 (goodA : restrictionAgrees S T A=true) (goodB : restrictionAgrees S T B=true)
 (below : PaidInstances.BelowBudget ordinary q)
 (F : Forest) (agree : agreement T S F=true) (ref : VertexGeometry.Refines F [A,B,C])
 (budget : F.length-1≤q) :
 ∃G,(runPair (PaidInstances.OwnPaid ordinary q) T S A B C q).answer=some G ∧
 agreement T S G=true ∧ VertexGeometry.Refines G [A,B,C] ∧ G.length≤F.length := by
 obtain ⟨H,K,runH,hq,hm,strict,runK,least⟩:=ContactedHard2DP.actual_remaining_C_call ordinary q
   T S A B C proper part emb goodA goodB below F agree ref budget
 obtain ⟨J,runJ,agreeJ,_,_⟩:=ContactedHard2DP.local_offset_competitors T S A B C proper part emb goodA goodB
 have jH : J=H := Option.some.inj (runJ.symm.trans runH)
 subst J
 have agreeK:=(GenericForest.solve_sound (PaidInstances.OwnPaid ordinary q) _ _ _ K runK).1
 have total:=pair_global_reconstruction T S A B C proper part emb cross H K agreeJ agreeK
 have budgetG : (H++K).length-1≤q := by simp only [List.length_append];omega
 refine ⟨H++K,?_,total.1,total.2,by simpa only [List.length_append] using least⟩
 simp only [runPair,if_pos hq,runH,if_pos hm,runK,Option.map_some,checked,Option.bind_some,
   accept,total.1,decide_eq_true budgetG,Bool.and_self,ite_true]

end ContactedGoodPair

-- Author integration type/axiom reports; proof text above is unchanged apart from recorded import edits.
set_option pp.universes true
#check @ContactedGoodPair.pair_global_reconstruction
#print axioms ContactedGoodPair.pair_global_reconstruction
#check @ContactedGoodPair.checked_sound
#print axioms ContactedGoodPair.checked_sound
#check @ContactedGoodPair.pair_complete
#print axioms ContactedGoodPair.pair_complete
