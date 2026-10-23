import Dispatcher
import PlannerControls

namespace Universal233.BothBad.DispatchControls
open RMAF Precontrols

/-- A planted finite callback, whose returned forests are checked against the
literal current ForestState. It is not a general exact solver. -/
def planted : ForestSolver := fun t ss b =>
  let F := ss.map leaves
  if ForestState.agrees t ss F && decide (ForestState.additionalCost ss F ≤ b) then some F
  else
    let G := [[4],[5],[6,7]]
    if ForestState.agrees t ss G && decide (ForestState.additionalCost ss G ≤ b) then some G
    else none

def run (q : Nat) := execute planted T S q (plan S T A B C D q)

theorem control_callbacks : ((run 5).calls.map Call.budget)=[2,0,0] := by decide
theorem control_original_answer : ((run 5).answer.map (fun F =>
    agreement T S F && decide (F.length-1=5)))=some true := by decide
theorem control_global_budget : (run 4).answer=none ∧ (run 3).answer=none ∧
    (run 2).answer=none := by decide
theorem control_no_free_whole_B : ((run 5).calls.map (fun c => c.sources.length))=[1,3,3] := by decide
theorem control_actual_callback_validity : ((run 5).calls.all (fun c =>
    match planted c.target c.sources c.budget with
    | none => false
    | some F => ForestState.agrees c.target c.sources F &&
        decide (ForestState.additionalCost c.sources F≤c.budget)))=true := by decide
end Universal233.BothBad.DispatchControls
