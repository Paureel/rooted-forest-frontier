import NonauthorConsumer
import Controls
import CutControls
import Lean
open Lean Elab Command
run_cmd do
  let env ← getEnv
  let modules : Array Name := #[`RMAF, `Geometry, `Bridge, `Composition, `CoreGraph, `CherryCoarsening, `CoreProgram, `CoreInvariants, `SourceBridge, `Contraction, `Normalization, `InitialLift, `Suppression, `EraseLift, `Origins, `Branches, `CutRecords, `FullTransport, `Coverage, `Entrypoint, `OutputBudget, `ColorBudget, `ColorSteps, `RawMass, `RationalMass, `Controls, `OriginalGraph, `Display, `Regions, `History, `Realization, `OwnerCover, `CutCoverage, `InitialCoverage, `Cost, `ValidPartition, `CutControls, `NonauthorConsumer]
  let mut count : Nat := 0
  for (n,ci) in env.constants do
    if let some idx := env.getModuleIdxFor? n then
      let origin := env.header.moduleNames[idx.toNat]!
      if modules.contains origin then
        match ci with
        | .thmInfo _ =>
          logInfo m!"PRINT_ORIGIN|{origin}|{n}"
          elabCommand (← `(command| #print axioms $(mkIdent n)))
          count := count + 1
        | _ => pure ()
  logInfo m!"PRINT_THEOREM_TOTAL|{count}"
