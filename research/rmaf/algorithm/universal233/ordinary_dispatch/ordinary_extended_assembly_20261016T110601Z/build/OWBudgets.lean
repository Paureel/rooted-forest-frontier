import OWControls
namespace OrdinaryDispatch.OptimizerLocalWork
open RMAF Universal233 WholeSourceWork CoreWork
open OrdinaryDispatch.BudgetOptimization

/-- Every queried callback budget, including failures, lies in the literal
start/fuel interval; this does not inspect or assume an accepted forest. -/
theorem scan_trial_budget_range (query : Nat→Option CommonForest) (start fuel b : Nat)
 (answer : Option CommonForest) (mem : (b,answer)∈(scan query start fuel).trials) :
 start≤b ∧ b<start+fuel := by
 induction fuel generalizing start with
 | zero=>simp [scan] at mem
 | succ fuel ih=>
  cases h:query start with
  | some F=>
   have eq : (b,answer)=(start,some F):=by simpa [scan,h] using mem
   have be:=congrArg Prod.fst eq
   constructor <;> omega
  | none=>
   have hm : (b,answer)=(start,none) ∨ (b,answer)∈(scan query (start+1) fuel).trials:=by
    simpa [scan,h] using mem
   rcases hm with eq|tail
   · have be:=congrArg Prod.fst eq;constructor <;> omega
   · have range:=ih (start+1) tail;constructor <;> omega

/-- Actual optimizer queries are bounded by original n, even on failed trials.
Malformed inputs have no trial; no bound by a reduced state is used. -/
theorem actual_trial_budget_cap (T S : Tree) (b : Nat) (answer : Option CommonForest)
 (mem : (b,answer)∈(optimize T S).search.trials) : b<(leaves T).length := by
 by_cases hp:DepthOne.proper T S=true
 · have hm : (b,answer)∈(scan (fun q=>FastOrdinary.solve q T S) 0 (leaves T).length).trials:=by
    simpa only [optimize,hp,ite_true,finish_search] using mem
   have range:=scan_trial_budget_range _ 0 (leaves T).length b answer hm
   omega
 · have hf:DepthOne.proper T S=false:=Bool.eq_false_iff.2 hp
   simp [optimize,hf] at mem
end OrdinaryDispatch.OptimizerLocalWork
