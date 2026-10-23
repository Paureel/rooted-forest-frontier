import BothBadBinding
import BindingPrecontrols
namespace Universal233.BothBadLocal.Controls
open RMAF BothBad BothBad.Precontrols
set_option maxRecDepth 10000
def lowF : ForestSolver := fun _ _ b=>if b≤2 then some [[999]] else none
def lowG : ForestSolver := fun _ _ b=>if b≤2 then some [[999]] else some []
theorem all_inputs_equal_low : ∀T ss b,b≤2 → lowF T ss b=lowG T ss b := by
 intro T ss b low
 simp [lowF,lowG,low]
theorem ordinary_all_inputs_local : ∀t s Q b,b≤2 →
 (ordinaryExecution lowF t s Q b).answer=(ordinaryExecution lowG t s Q b).answer :=
 fun t s Q b low=>ordinaryExecution_answer_congr_at lowF lowG 2 all_inputs_equal_low t s Q b low
theorem low_ordinary_answer : (ordinaryExecution lowF T S [leaves S] 2).answer=some [[999]] := by decide
theorem high_f_none : (ordinaryExecution lowF T S [leaves S] 3).answer=none := by decide
theorem high_g_some : (ordinaryExecution lowG T S [leaves S] 3).answer=some [] := by decide
theorem literal_full_payment : (plan S T A B C (PairGeometry.descendants T edge.2) 5).map
 (fun e=>e.budget+e.output.sourceCuts.length+e.mode.extra)=[5,5,5] := by decide
theorem retained_extra_paid : (plan S T A B C (PairGeometry.descendants T edge.2) 5).map (fun e=>e.mode.extra)=[0,1,1] := by decide
theorem zero_budget_runtime : (runPair malformedActual S T A B C edge 0).answer=none := by decide
theorem zero_budget_ih : BelowIH 0 malformedActual := by intro r low; omega
theorem completion_preserves_malformed_low :
 ForestMinCompletion.ghost 2 malformedActual (.leaf 0) (.leaf 1) 0=some [[999]] := by
 rw [ForestMinCompletion.ghost_eq_actual 2 malformedActual _ _ 0 (by decide)]
 rfl
#check ordinary_candidate_local
#check ordinary_candidate_below
#check forest_exact_at_local
#check solvePair_conditional_cover
#check solvePair_minimum
#check solvePair_calls_strict
#check solvePair_trace_mass
end Universal233.BothBadLocal.Controls
