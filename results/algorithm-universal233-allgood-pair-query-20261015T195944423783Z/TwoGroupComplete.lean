import TwoGroupDP
namespace OrdinaryDispatch.GoodPairDP
open RMAF ForestState ForestGroups RestrictionBridge Universal233

theorem local_mono (actual : Ordinary) {b r : Nat}
 (ih : ForestMinCompletion.LocalOrdinaryIH b actual) (low : r≤b) :
 ForestMinCompletion.LocalOrdinaryIH r actual := by
 refine ⟨?_,?_⟩
 · intro t s k F le prop ans
   exact ih.sound t s k F (Nat.le_trans le low) prop ans
 · intro t s k F le prop ha hb
   exact ih.complete t s k F (Nat.le_trans le low) prop ha hb

theorem solve_complete (actual : Ordinary) (T : Option Tree) (ss : List Tree) (U V : List Nat) (b : Nat)
 (ih : ForestMinCompletion.LocalOrdinaryIH b actual)
 (hq : partitionCheck (labels T) [U,V]=true) (own : Owns ss [U,V])
 (good : AllGoodDP.allGood (localTarget T U) (owned ss U)=true)
 (F : Forest) (hf : agrees T ss F=true) (budget : additionalCost ss F≤b) :
 ∃G,solve actual T ss U V b=some G ∧ G.length≤F.length := by
 obtain ⟨H,hH,hvalid,hbal,hmin⟩ := AllGoodDP.run_total_exact _ _ good
 obtain ⟨hu,hv,bill⟩ := two_forward T ss U V F hq own hf
 have minU := hmin _ hu
 have affordable : additionalCost (owned ss U) H≤b := by omega
 have budgetV : additionalCost (owned ss V) (family V F)≤b-additionalCost (owned ss U) H := by omega
 obtain ⟨K,hK,kmin⟩ := GenericForest.LocalIH.exact_at_current_budget actual _
  (local_mono actual ih (Nat.sub_le _ _)) (localTarget T V) (owned ss V) (family V F) hv budgetV
 have ulen := ForestGroups.sources_le_blocks _ _ _ hu
 have hlen : H.length≤(family U F).length := by
  simp only [additionalCost] at minU hbal
  omega
 have lenF := total_family_length (labels T) F [U,V] (agrees_parts T ss F hf).2.1 hq
  (state_refines T ss F [U,V] hf own)
 simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,Nat.add_zero] at lenF
 refine ⟨H++K,?_,?_⟩
 · simp [solve,hH,affordable,hK]
 · simp only [List.length_append]
   omega

theorem solve_feasible_iff (actual : Ordinary) (T : Option Tree) (ss : List Tree) (U V : List Nat) (b : Nat)
 (ih : ForestMinCompletion.LocalOrdinaryIH b actual)
 (hp : proper T ss=true) (hq : partitionCheck (labels T) [U,V]=true)
 (own : Owns ss [U,V]) (cross : CrossClear T ss [U,V])
 (good : AllGoodDP.allGood (localTarget T U) (owned ss U)=true) :
 (∃G,solve actual T ss U V b=some G) ↔ ∃F,agrees T ss F=true ∧ additionalCost ss F≤b := by
 constructor
 · rintro ⟨G,hG⟩
   have h := solve_sound actual T ss U V b ih hp hq own cross good G hG
   exact ⟨G,h.1,h.2.1⟩
 · rintro ⟨F,hf,hb⟩
   obtain ⟨G,hG,_⟩ := solve_complete actual T ss U V b ih hq own good F hf hb
   exact ⟨G,hG⟩
end OrdinaryDispatch.GoodPairDP
