import Lean
import ExplicitSourceOptimizer
import MeterAudit
open Lean Elab Command

/- One-shot dependency audit. Reuses Lean's getUsedConstants and environment
   APIs, following Lean/Util/CollectAxioms.lean, without replacing the toolkit. -/
partial def collectReachable (env : Environment) (pending : List Name) (seen : NameSet) : NameSet :=
  match pending with
  | [] => seen
  | n::ns =>
    if seen.contains n then collectReachable env ns seen
    else
      let seen := seen.insert n
      match env.find? n with
      | none => collectReachable env ns seen
      | some ci =>
        let valueDeps := match ci.value? true with
          | none => #[]
          | some e => e.getUsedConstants
        collectReachable env ((ci.type.getUsedConstants ++ valueDeps).toList ++ ns) seen

run_cmd do
  let env ← getEnv
  let forbidden := #[
    ``OrdinaryDispatch.CompleteSource.completeSourceOptimize_bound,
    ``OrdinaryDispatch.GlobalSourceAssembly.sourceOptimize_uniform_233,
    ``OrdinaryDispatch.FastOrdinary.solve_exact,
    ``OrdinaryDispatch.BudgetOptimization.optimization_exact,
    ``OrdinaryDispatch.BudgetOptimization.selected_minimum,
    ``OrdinaryDispatch.BudgetOptimization.scan_upper_success,
    ``OrdinaryDispatch.RecoveryLocalWork.optimizer_recovery_once_bound,
    ``OrdinaryDispatch.RecoveryLocalWork.optimizer_recovery_233,
    ``OrdinaryDispatch.CompleteSource.completeSourceCounter_bound,
    ``OrdinaryDispatch.CompleteSource.completeSourceQuery_bound,
    ``sorryAx]
  for root in #[``ExplicitSourceOptimizer20261022.optimum_k_source_bound,
      ``RebasedSourceCounter20261022.completeSourceCounter_bound,
      ``SourceMeterAudit20261022.source_counter_actual_step,
      ``SourceMeterAudit20261022.actual_common_equalbudget_retained] do
    let reached := collectReachable env [root] {}
    let missing := reached.toArray.filter (fun n=>(env.find? n).isNone)
    let hits := forbidden.filter reached.contains
    logInfo m!"FINAL_ROOT {root} reached={reached.toArray.size} missing={missing} forbidden={hits}"
    unless missing.isEmpty && hits.isEmpty do throwError "Final proof reference/dependency audit failed"
  logInfo "FINAL_SOURCE_AUDIT: 4/4 roots, no missing references, no forbidden roots"
