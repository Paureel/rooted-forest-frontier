import Planner
import BothPrecontrols
namespace Universal233.BothBad.PlannerControls
open RMAF Precontrols
theorem control_cached_cheap : ((RankConsumer.fourProbe S (BinaryCheap.cheapColor A B D)).outputs.map (fun o => o.sourceCuts.length))=[3] ∧
    (RankConsumer.fourProbe S (BinaryCheap.cheapColor B A D)).outputs=[] := by decide
theorem control_discovered_one : (knownOne T S A).isSome=true := by decide
theorem control_paid_opposite : chargedCosts (plan S T A B C D 5)=[3,5,5] ∧
    budgets (plan S T A B C D 5)=[2,0,0] := by decide
theorem control_prune_before_subtract : chargedCosts (plan S T A B C D 4)=[3] ∧
    budgets (plan S T A B C D 4)=[1] := by decide
theorem control_low_budget : chargedCosts (plan S T A B C D 2)=[] := by decide
theorem control_minimum_cost_boundary : chargedCosts (plan S T A B C D 3)=[3] ∧
    budgets (plan S T A B C D 3)=[0] := by decide
end Universal233.BothBad.PlannerControls
