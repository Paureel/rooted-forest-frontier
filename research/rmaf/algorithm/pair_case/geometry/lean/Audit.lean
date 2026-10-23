import Lean
import Controls
open Lean Elab Command
run_cmd do
  let env ← getEnv
  let wanted := ["RMAF", "Geometry", "Bridge", "Selector", "Controls"]
  for (name,info) in env.constants.toList do
    match env.getModuleIdxFor? name with
    | none => pure ()
    | some idx =>
      let origin := env.header.moduleNames[idx.toNat]!
      if wanted.contains origin.toString then
        let axs ← collectAxioms name
        let axnames := String.intercalate "," (axs.toList.map Name.toString)
        logInfo m!"ORIGIN-AUDIT|{origin}|{name}|{info.isAxiom}|{axnames}"
