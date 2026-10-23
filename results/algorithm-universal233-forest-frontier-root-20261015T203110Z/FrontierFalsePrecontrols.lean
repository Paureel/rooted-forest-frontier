import FrontierPrecontrols
namespace GenericForest.FrontierControls
open RMAF Universal233 Universal233.PaidQueries
example : (meterSchedule fail work 4 [.hard 8,.hard 9]).queries=[] := by decide
example : (meterSchedule success work 4 [.hard 8,.hard 8]).queries=[(8,2)] := by decide
example : (meterSchedule fail work 2 [.hard 8]).queries=[(8,1)] := by decide
example : (meterSchedule fail work 4 [.hard 8,.hard 9]).recursiveWork=0 := by decide
example : (1:Rat)-2/(2:Rat)>0 := by
 rw [endpoint_denominator_zero]; decide
end GenericForest.FrontierControls
