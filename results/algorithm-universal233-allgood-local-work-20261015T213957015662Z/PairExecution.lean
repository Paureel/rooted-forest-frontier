import ActualPair
import MassAssembly
namespace OrdinaryDispatch.GoodPairDP
open RMAF ForestState ForestGroups RestrictionBridge Universal233 Universal233.BothBad

def runPair (actual : Ordinary) (T S : Tree) (A B C : List Nat) (q : Nat) : Execution :=
 if 2≤q then
  let ss := OutputState.sourceForest S [A,B,C]
  match AllGoodDP.run (localTarget (some T) (A++B)) (owned ss (A++B)) with
  | none => ⟨none,[]⟩
  | some H =>
   let m := additionalCost (owned ss (A++B)) H
   if m≤q-2 then
    let r := q-2-m
    let target := localTarget (some T) C
    let sources := owned ss C
    ⟨checked T S q ((GenericForest.solve actual target sources r).map (fun K=>H++K)),[⟨target,sources,r⟩]⟩
   else ⟨none,[]⟩
 else ⟨none,[]⟩

theorem runPair_answer (actual : Ordinary) (T S : Tree) (A B C : List Nat) (q : Nat) :
 (runPair actual T S A B C q).answer=
 if 2≤q then checked T S q (solve actual (some T) (OutputState.sourceForest S [A,B,C]) (A++B) C (q-2)) else none := by
 by_cases affordable : 2≤q
 · simp only [runPair,affordable,ite_true]
   try dsimp only
   cases h : AllGoodDP.run (localTarget (some T) (A++B)) (owned (OutputState.sourceForest S [A,B,C]) (A++B)) with
   | none => simp [solve,h,checked]
   | some H =>
    by_cases hm : additionalCost (owned (OutputState.sourceForest S [A,B,C]) (A++B)) H≤q-2
    · simp [solve,h,hm]
    · simp [solve,h,hm,checked]
 · simp [runPair,affordable]

theorem runPair_sound (actual : Ordinary) (T S : Tree) (A B C : List Nat) (q : Nat) (F : Forest)
 (answer : (runPair actual T S A B C q).answer=some F) : agreement T S F=true ∧ F.length-1≤q := by
 rw [runPair_answer] at answer
 split at answer
 · exact (checked_sound T S q _ F answer).2
 · contradiction

theorem runPair_mass (actual : Ordinary) (T S : Tree) (A B C : List Nat) (q : Nat)
 (hs : (leaves S).Nodup) (ht : (leaves T).Nodup)
 (same : ∀x,x∈leaves T ↔ x∈leaves S)
 (hp : partitionCheck (leaves S) [A,B,C]=true)
 (hac : BinaryExchange.Disj T A C) (hbc : BinaryExchange.Disj T B C)
 (ga : restrictionAgrees T S A=true) (gb : restrictionAgrees T S B=true)
 (over : ∃v,v∈minimalVertices A T ∧ v∈minimalVertices B T)
 (c : Rat) (hc : 2≤c) : traceMass c q (runPair actual T S A B C q).calls≤c^(-3 : Int) := by
 have zero : (0 : Rat)≤c^(-3 : Int) := Rat.le_of_lt (Rat.zpow_pos (by grind : 0<c))
 obtain ⟨good,pos⟩ := actual_good_pair T S A B C hs ht same hp hac hbc ga gb over
 obtain ⟨H,hH,hvalid,_,_⟩ := AllGoodDP.run_total_exact _ _ good
 have positive := pos H hvalid
 unfold runPair
 try dsimp only
 split
 · rename_i affordable
   rw [hH]
   try dsimp only
   split
   · rename_i enough
     have low : 3≤q-(q-2-additionalCost (owned (OutputState.sourceForest S [A,B,C]) (A++B)) H) := by omega
     have bound := PaidQueries.negpow_antitone c hc 3
      (q-(q-2-additionalCost (owned (OutputState.sourceForest S [A,B,C]) (A++B)) H)) low
     simpa [traceMass,PaidQueries.actualQueryMass,Rat.add_zero] using bound
   · simpa [traceMass,PaidQueries.actualQueryMass,Rat.add_zero] using zero
 · simpa [traceMass,PaidQueries.actualQueryMass,Rat.add_zero] using zero

theorem runPair_calls_decrease (actual : Ordinary) (T S : Tree) (A B C : List Nat) (q : Nat)
 (a : Call) (mem : a∈(runPair actual T S A B C q).calls) : a.budget<q := by
 unfold runPair at mem
 try dsimp only at mem
 split at mem
 · try dsimp only at mem
   split at mem
   · simp at mem
   · try dsimp only at mem
     split at mem
     · have eq := congrArg Call.budget (List.mem_singleton.mp mem)
       dsimp at eq
       omega
     · simp at mem
 · simp at mem
end OrdinaryDispatch.GoodPairDP
