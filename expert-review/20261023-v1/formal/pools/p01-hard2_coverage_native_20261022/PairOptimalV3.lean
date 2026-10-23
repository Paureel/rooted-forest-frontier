import ActualGoodPairV2
open RMAF ForestState ForestGroups RestrictionBridge Universal233
namespace ContactedGoodPair

theorem checked_preserves {T S : Tree} {q : Nat} {o : Option Forest} {F : Forest}
 (h : checked T S q o=some F) : o=some F := by
 cases o with
 | none => simp [checked] at h
 | some G =>
  by_cases good : accept T S q G=true
  · simpa [checked,good] using h
  · simp [checked,good] at h

theorem local_dp_return_agrees (T : Option Tree) (ss : List Tree) (H : Forest)
 (h : AllGoodDP.run T ss=some H) : agrees T ss H=true := by
 by_cases hg : AllGoodDP.allGood T ss=true
 · obtain ⟨J,runJ,agreeJ,_,_⟩:=AllGoodDP.run_total_exact T ss hg
   have eq : J=H := Option.some.inj (runJ.symm.trans h)
   simpa only [eq] using agreeJ
 · simp [AllGoodDP.run,hg] at h

theorem pair_some_witness (actual : Ordinary) (T S : Tree) (A B C : List Nat) (q : Nat) (F : Forest)
 (returned : (runPair actual T S A B C q).answer=some F) :
 let ss:=OutputState.sourceForest S [A,B,C]
 ∃H K,AllGoodDP.run (localTarget (some T) (A++B)) (owned ss (A++B))=some H ∧
 GenericForest.solve actual (localTarget (some T) C) (owned ss C)
   (q-2-additionalCost (owned ss (A++B)) H)=some K ∧
 F=H++K ∧ agreement T S F=true ∧ F.length-1≤q := by
 dsimp only
 unfold runPair at returned
 split at returned
 · rename_i hq
   cases runH : AllGoodDP.run (localTarget (some T) (A++B))
     (owned (OutputState.sourceForest S [A,B,C]) (A++B)) with
   | none => simp only [runH] at returned;cases returned
   | some H =>
     simp only [runH] at returned
     split at returned
     · rename_i hm
       cases runK : GenericForest.solve actual (localTarget (some T) C)
         (owned (OutputState.sourceForest S [A,B,C]) C)
         (q-2-additionalCost (owned (OutputState.sourceForest S [A,B,C]) (A++B)) H) with
       | none => simp only [runK,Option.map_none,checked,Option.bind_none] at returned;cases returned
       | some K =>
         simp only [runK,Option.map_some] at returned
         have eq : H++K=F := Option.some.inj (checked_preserves returned)
         have sound:=checked_sound returned
         exact ⟨H,K,rfl,runK,eq.symm,sound⟩
     · cases returned
 · cases returned

theorem pair_some_sound (actual : Ordinary) (T S : Tree) (A B C : List Nat) (q : Nat) (G : Forest)
 (proper : DepthOne.proper T S=true) (part : partitionCheck (leaves S) [A,B,C]=true)
 (emb : pairwiseEmbeddings S [A,B,C]=true)
 (cross : CrossClear (some T) (OutputState.sourceForest S [A,B,C]) [A++B,C])
 (returned : (runPair actual T S A B C q).answer=some G) :
 agreement T S G=true ∧ VertexGeometry.Refines G [A,B,C] ∧ G.length-1≤q := by
 obtain ⟨H,K,runH,runK,eq,agree,budget⟩:=pair_some_witness actual T S A B C q G returned
 have ha:=local_dp_return_agrees _ _ H runH
 have hb:=(GenericForest.solve_sound actual _ _ _ K runK).1
 have total:=pair_global_reconstruction T S A B C proper part emb cross H K ha hb
 exact ⟨agree,eq.symm ▸ total.2,budget⟩

theorem pair_some_minimum (ordinary : PaidInstances.OrdinarySolver) (q : Nat)
 (T S : Tree) (A B C : List Nat)
 (proper : DepthOne.proper T S=true) (part : partitionCheck (leaves S) [A,B,C]=true)
 (emb : pairwiseEmbeddings S [A,B,C]=true)
 (cross : CrossClear (some T) (OutputState.sourceForest S [A,B,C]) [A++B,C])
 (goodA : restrictionAgrees S T A=true) (goodB : restrictionAgrees S T B=true)
 (below : PaidInstances.BelowBudget ordinary q) (G : Forest)
 (returned : (runPair (PaidInstances.OwnPaid ordinary q) T S A B C q).answer=some G) :
 agreement T S G=true ∧ VertexGeometry.Refines G [A,B,C] ∧ G.length-1≤q ∧
 ∀F,agreement T S F=true→VertexGeometry.Refines F [A,B,C]→G.length≤F.length := by
 have sound:=pair_some_sound _ T S A B C q G proper part emb cross returned
 refine ⟨sound.1,sound.2.1,sound.2.2,?_⟩
 intro F agree ref
 by_cases budget : F.length-1≤q
 · obtain ⟨J,runJ,_,_,least⟩:=pair_complete ordinary q T S A B C proper part emb cross goodA goodB below F agree ref budget
   have eq : J=G := Option.some.inj (runJ.symm.trans returned)
   simpa only [eq] using least
 · have bound:=sound.2.2;omega

theorem pair_none_iff (ordinary : PaidInstances.OrdinarySolver) (q : Nat)
 (T S : Tree) (A B C : List Nat)
 (proper : DepthOne.proper T S=true) (part : partitionCheck (leaves S) [A,B,C]=true)
 (emb : pairwiseEmbeddings S [A,B,C]=true)
 (cross : CrossClear (some T) (OutputState.sourceForest S [A,B,C]) [A++B,C])
 (goodA : restrictionAgrees S T A=true) (goodB : restrictionAgrees S T B=true)
 (below : PaidInstances.BelowBudget ordinary q) :
 (runPair (PaidInstances.OwnPaid ordinary q) T S A B C q).answer=none ↔
 ¬∃F,agreement T S F=true ∧ VertexGeometry.Refines F [A,B,C] ∧ F.length-1≤q := by
 constructor
 · intro no ⟨F,agree,ref,budget⟩
   obtain ⟨G,yes,_,_,_⟩:=pair_complete ordinary q T S A B C proper part emb cross goodA goodB below F agree ref budget
   rw [no] at yes
   cases yes
 · intro infeasible
   cases returned : (runPair (PaidInstances.OwnPaid ordinary q) T S A B C q).answer with
   | none => rfl
   | some G =>
     have sound:=pair_some_sound _ T S A B C q G proper part emb cross returned
     exact False.elim (infeasible ⟨G,sound⟩)
end ContactedGoodPair

-- Author integration type/axiom reports; proof text above is unchanged apart from recorded import edits.
set_option pp.universes true
#check @ContactedGoodPair.checked_preserves
#print axioms ContactedGoodPair.checked_preserves
#check @ContactedGoodPair.local_dp_return_agrees
#print axioms ContactedGoodPair.local_dp_return_agrees
#check @ContactedGoodPair.pair_some_witness
#print axioms ContactedGoodPair.pair_some_witness
#check @ContactedGoodPair.pair_some_sound
#print axioms ContactedGoodPair.pair_some_sound
#check @ContactedGoodPair.pair_some_minimum
#print axioms ContactedGoodPair.pair_some_minimum
#check @ContactedGoodPair.pair_none_iff
#print axioms ContactedGoodPair.pair_none_iff
