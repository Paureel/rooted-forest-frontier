import ERControls
import Lean
open Lean Elab Command
run_cmd do
 let env ← getEnv
 for n in [`Universal233.CherryBranching.select,`Universal233.CherryBranching.cherries,`Universal233.CherryBranching.candidates,`Universal233.HardParent.pendantOriginal,`RMAF.best,`RMAF.agreement] do
  let origin := match env.getModuleIdxFor? n with | some k => env.header.moduleNames[k.toNat]!.toString | none => "<unresolved>"
  logInfo m!"SOURCE_ORIGIN|{n}|{origin}"
