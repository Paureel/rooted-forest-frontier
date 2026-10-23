import BOForest
namespace OrdinaryDispatch.BudgetOptimization
open RMAF Universal233

abbrev Trial := Nat × Option CommonForest
structure Scan where
 selected : Option (Nat × CommonForest)
 trials : List Trial
 deriving Repr

/-- Actual iteration: each query is evaluated once and retained before branching.
The remaining length decreases on a failed query. No cut recovery occurs here. -/
def scan (query : Nat → Option CommonForest) (start : Nat) : Nat → Scan
 | 0 => ⟨none,[]⟩
 | fuel+1 =>
   let answer := query start
   match answer with
   | some F => ⟨some (start,F),[(start,answer)]⟩
   | none =>
     let tail := scan query (start+1) fuel
     ⟨tail.selected,(start,answer)::tail.trials⟩

def failedTrials (start : Nat) : Nat → List Trial
 | 0 => []
 | n+1 => (start,none)::failedTrials (start+1) n

theorem failed_length (start n : Nat) : (failedTrials start n).length=n := by
 induction n generalizing start with
 | zero => rfl
 | succ n ih => simp [failedTrials,ih]

theorem scan_success (query : Nat → Option CommonForest) (fuel start q : Nat) (F : CommonForest)
 (h : (scan query start fuel).selected=some (q,F)) :
 ∃ skipped, q=start+skipped ∧ skipped<fuel ∧
 (scan query start fuel).trials=failedTrials start skipped++[(q,some F)] ∧
 query q=some F ∧ (∀b,start≤b → b<q → query b=none) := by
 induction fuel generalizing start with
 | zero => simp [scan] at h
 | succ fuel ih =>
   cases answer : query start with
   | some G =>
     have eq : (start,G)=(q,F) := by simpa [scan,answer] using h
     have sq : start=q := congrArg Prod.fst eq
     have gf : G=F := congrArg Prod.snd eq
     subst q;subst F
     refine ⟨0,by omega,by omega,?_,answer,?_⟩
     · simp [scan,answer,failedTrials]
     · intro b hb hlt;omega
   | none =>
     have ht : (scan query (start+1) fuel).selected=some (q,F) := by simpa [scan,answer] using h
     obtain ⟨sk,eq,lt,tr,yes,no⟩ := ih (start+1) ht
     refine ⟨sk+1,by omega,by omega,?_,yes,?_⟩
     · simp [scan,answer,failedTrials,tr]
     · intro b hb hlt
       by_cases same : b=start
       · simpa [same] using answer
       · exact no b (by omega) hlt

theorem scan_failure (query : Nat → Option CommonForest) (fuel start : Nat)
 (h : (scan query start fuel).selected=none) :
 (scan query start fuel).trials=failedTrials start fuel ∧
 ∀b,start≤b → b<start+fuel → query b=none := by
 induction fuel generalizing start with
 | zero => exact ⟨rfl,by intro b hb hlt;omega⟩
 | succ fuel ih =>
   cases answer : query start with
   | some G => simp [scan,answer] at h
   | none =>
     have ht : (scan query (start+1) fuel).selected=none := by simpa [scan,answer] using h
     obtain ⟨tr,no⟩ := ih (start+1) ht
     refine ⟨by simp [scan,answer,failedTrials,tr],?_⟩
     intro b hb hlt
     by_cases same : b=start
     · simpa [same] using answer
     · exact no b (by omega) (by omega)

theorem scan_complete (query : Nat → Option CommonForest) (fuel start b : Nat)
 (low : start≤b) (high : b<start+fuel) (yes : ∃F,query b=some F) :
 ∃q F,(scan query start fuel).selected=some (q,F) := by
 cases h : (scan query start fuel).selected with
 | none =>
   have no := (scan_failure query fuel start h).2 b low high
   obtain ⟨F,found⟩ := yes
   rw [no] at found
   contradiction
 | some p => exact ⟨p.1,p.2,h⟩

theorem failed_budget_trace (start n : Nat) :
 (failedTrials start n).map Prod.fst=List.range' start n := by
 induction n generalizing start with
 | zero => rfl
 | succ n ih => simp [failedTrials,List.range'_succ,ih]

end OrdinaryDispatch.BudgetOptimization
