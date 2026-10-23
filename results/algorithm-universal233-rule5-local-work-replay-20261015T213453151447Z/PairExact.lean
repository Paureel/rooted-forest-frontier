import PairExecution
namespace OrdinaryDispatch.GoodPairDP
open RMAF ForestState ForestGroups RestrictionBridge Universal233 Universal233.BothBad
abbrev BelowIH (q : Nat) (actual : Ordinary) := ∀r,r<q→ForestMinCompletion.LocalOrdinaryIH r actual

theorem runPair_complete (actual : Ordinary) (T S : Tree) (A B C : List Nat) (q : Nat)
 (below : BelowIH q actual)
 (hs : (leaves S).Nodup) (ht : (leaves T).Nodup)
 (same : ∀x,x∈leaves T ↔ x∈leaves S)
 (hp : partitionCheck (leaves S) [A,B,C]=true)
 (es : pairwiseEmbeddings S [A,B,C]=true)
 (hac : BinaryExchange.Disj T A C) (hbc : BinaryExchange.Disj T B C)
 (ga : restrictionAgrees T S A=true) (gb : restrictionAgrees T S B=true)
 (over : ∃v,v∈minimalVertices A T ∧ v∈minimalVertices B T)
 (F : Forest) (hf : agreement T S F=true) (refF : Refines F [A,B,C]) (budget : F.length-1≤q) :
 ∃G,(runPair actual T S A B C q).answer=some G ∧ G.length≤F.length := by
 let ss := OutputState.sourceForest S [A,B,C]
 have ref : SourceCoverage.RefinesBlocks [A,B,C] [A,B,C] := fun K hk=>⟨K,hk,List.Subset.refl _⟩
 obtain ⟨proper,hq,own,cross⟩ := GroupedFullQuery.abc_geometry T S [A,B,C] A B C hs ht same hp hp ref hac hbc
 have fstate := OutputState.original_to_state T S [A,B,C] F ht hs same hp hf refF
 have sslen : ss.length=3 := by simpa [ss] using (OutputState.checked_materialization S [A,B,C] hs hp).1
 have flen := ForestGroups.sources_le_blocks (some T) ss F fstate
 have affordable : 2≤q := by omega
 have ib : ForestMinCompletion.LocalOrdinaryIH (q-2) actual := below (q-2) (by omega)
 have good := (actual_good_pair T S A B C hs ht same hp hac hbc ga gb over).1
 obtain ⟨G,hG,glen⟩ := solve_complete actual (some T) ss (A++B) C (q-2) ib hq own good F fstate
  (by simp only [additionalCost];omega)
 have gs := solve_sound actual (some T) ss (A++B) C (q-2) ib proper hq own cross good G hG
 have gorig := (OutputState.state_to_original T S [A,B,C] G hs same hp es gs.1).1
 have gl := ForestGroups.sources_le_blocks _ _ _ gs.1
 have gbudget : G.length-1≤q := by
  have hb := gs.2.1
  simp only [additionalCost] at hb
  omega
 refine ⟨G,?_,glen⟩
 rw [runPair_answer]
 simp only [affordable,ite_true]
 rw [hG]
 exact checked_complete T S q G gorig gbudget

theorem runPair_minimum (actual : Ordinary) (T S : Tree) (A B C : List Nat) (q : Nat)
 (below : BelowIH q actual)
 (hs : (leaves S).Nodup) (ht : (leaves T).Nodup)
 (same : ∀x,x∈leaves T ↔ x∈leaves S)
 (hp : partitionCheck (leaves S) [A,B,C]=true) (es : pairwiseEmbeddings S [A,B,C]=true)
 (hac : BinaryExchange.Disj T A C) (hbc : BinaryExchange.Disj T B C)
 (ga : restrictionAgrees T S A=true) (gb : restrictionAgrees T S B=true)
 (over : ∃v,v∈minimalVertices A T ∧ v∈minimalVertices B T)
 (G : Forest) (answer : (runPair actual T S A B C q).answer=some G) :
 agreement T S G=true ∧ G.length-1≤q ∧
 ∀F,agreement T S F=true→Refines F [A,B,C]→G.length≤F.length := by
 have gs := runPair_sound actual T S A B C q G answer
 refine ⟨gs.1,gs.2,?_⟩
 intro F hf href
 by_cases budget : F.length-1≤q
 · obtain ⟨H,hH,min⟩ := runPair_complete actual T S A B C q below hs ht same hp es hac hbc ga gb over F hf href budget
   have eq : H=G := Option.some.inj (hH.symm.trans answer)
   simpa [eq] using min
 · omega
end OrdinaryDispatch.GoodPairDP
