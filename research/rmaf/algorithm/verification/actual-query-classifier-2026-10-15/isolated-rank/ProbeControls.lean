import OptimizedWork
import ProbePrecontrols
namespace Universal233.RankConsumer.Controls
open RMAF CoreProgram SourceCoverage RankDichotomy CoreWork

def fourCheap : Tree := .node (.node (.leaf 0) (.leaf 1))
    (.node (.node (.node (.leaf 2) (.leaf 3)) (.node (.leaf 4) (.leaf 5))) (.node (.leaf 6) (.leaf 7)))
def fourHigh : Tree := .node (.node (.leaf 0) (.leaf 1))
    (.node (.node (.node (.leaf 2) (.leaf 4)) (.node (.leaf 3) (.leaf 5))) (.node (.leaf 6) (.leaf 7)))
def tagged (x : Nat) : Nat := if x<2 then 0 else if x<6 then (if x<4 then 1 else 4) else 2

theorem control_four_cheap_probe : fourAccepted fourCheap tagged = true ∧
    (fourProbe fourCheap tagged).outputs.map (fun o => o.sourceCuts.length) = [3] := by decide

theorem control_four_high_probe : fourAccepted fourHigh tagged = false ∧
    (generate fourHigh tagged 7).outputs.map (fun o => o.sourceCuts.length) = [4,4] := by decide

theorem control_cheap_exact_all_budgets (q : Nat) :
    optimizedFourOutputs fourCheap tagged q = (generate fourCheap tagged q).outputs :=
  optimized_four_exact fourCheap tagged (by decide) (by decide) q

theorem control_high_exact_all_budgets (q : Nat) :
    optimizedFourOutputs fourHigh tagged q = (generate fourHigh tagged q).outputs :=
  optimized_four_exact fourHigh tagged (by decide) (by decide) q

theorem control_high_literal_mass :
    rawQMass (mkRat 233 100) (generate fourHigh tagged 7).outputs ≤ 2*(mkRat 233 100)^(-4 : Int) :=
  (four_rejected_high fourHigh tagged (by decide) (by decide) control_four_high_probe.1 7 (mkRat 233 100) (by decide)).2

theorem control_actual_fixed_probe_model :
    (meterGenerate fourHigh tagged 3).measured.work ≤ initialCharge fourHigh+64*(cap (inputResource fourHigh)+6) :=
  four_probe_model_work fourHigh tagged (by decide)

theorem control_repeated_hypothesis_essential : accepted repeated (fun _ => 0) = false ∧
    RankFeasible repeated (fun _ => 0) := ⟨by decide,repeated_bare_feasible⟩

theorem control_actual_low_no_color_calls :
    (meterOptimizedFour fourHigh tagged 2).colorCalls = 0 := by decide

theorem control_actual_cheap_color_calls :
    (meterOptimizedFour fourCheap tagged 7).colorCalls = 8 := by decide

theorem control_actual_high_color_calls :
    (meterOptimizedFour fourHigh tagged 7).colorCalls = 16 := by decide

private theorem private_origin_control : 2+2=4 := by decide
theorem control_private_origin : 2+2=4 := private_origin_control
end Universal233.RankConsumer.Controls
