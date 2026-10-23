import BothConsumers
namespace Universal233.BothBad.ActualConsumers
open RMAF DispatchControls Precontrols
theorem false_actual_call_cost : (profilePair planted Call.budget S T A B C selectedEdge 5).recursiveWork=3 := by decide
theorem false_one_core_query : (coreRequests S A B D 5).map CoreRequest.budget=[3,3] := by decide
theorem false_budget_reuse : ((solvePair planted S T A B C selectedEdge 5).calls.map Call.budget)=[2,1,1] := by decide
end Universal233.BothBad.ActualConsumers
