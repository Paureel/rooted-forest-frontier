import LeanAxiomPlant
import LeanCleanControl
import Lean
open Lean Elab Command

run_cmd do
  let env ← getEnv
  for name in [`pair14_clean_arithmetic_control, `pair14_clean_multiplicity_control,
      `pair14_contaminated_false_control] do
    let axs ← collectAxioms name
    logInfo m!"CONTROLAUDIT|{name}|{axs.toList}"
    for a in axs do
      unless a == `propext || a == `Quot.sound || a == `Classical.choice do
        throwError m!"REJECT_CUSTOM_AXIOM|{name}|{a}"
