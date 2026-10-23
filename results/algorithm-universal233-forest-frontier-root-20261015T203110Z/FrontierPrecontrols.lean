import ForestTrace
namespace GenericForest.FrontierControls
open RMAF Universal233 Universal233.PaidQueries
set_option maxRecDepth 10000
def fail (_ : Nat) (_ : Nat) : Option (Nat × Nat) := none
def success (_ : Nat) (_ : Nat) : Option (Nat × Nat) := some (2,7)
def work (_ : Nat) (q : Nat) := q+3

theorem failed_query_retained : (meterSchedule fail work 4 [.hard 8,.hard 9]).queries=[(8,2)] ∧
 (meterSchedule fail work 4 [.hard 8,.hard 9]).recursiveWork=5 := by decide

theorem successful_queries_both : (meterSchedule success work 4 [.hard 8,.hard 8]).queries=[(8,2),(8,2)] ∧
 (meterSchedule success work 4 [.hard 8,.hard 8]).recursiveWork=10 := by decide

theorem singleton_no_discount : (meterSchedule fail work 2 [.hard 8]).queries=[(8,2)] := by decide

theorem pruned_no_queries : (meterSchedule fail work 3 [.hard 8,.hard 9]).queries=[] := by decide

theorem geometric_planted : (1:Rat)-2/(3:Rat)>0 ∧ ((1:Rat)-2/(3:Rat))⁻¹=3 := by decide +kernel

theorem endpoint_denominator_zero : (1:Rat)-2/(2:Rat)=0 := by decide +kernel
end GenericForest.FrontierControls
