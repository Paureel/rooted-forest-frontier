import RMAF
import Geometry
import Bridge
import Composition
import CoreGraph
import CherryCoarsening
import CoreProgram
import CoreInvariants
import SourceBridge
import Contraction
import Normalization
import InitialLift
import Suppression
import EraseLift
import Origins
import Branches
import CutRecords
import FullTransport
import Coverage
import Entrypoint
import OutputBudget
import ColorBudget
import ColorSteps
import RawMass
import RationalMass
import ParentColors
import OriginalGraph
import Display
import Regions
import History
import Realization
import OwnerCover
import CutCoverage
import InitialCoverage
import Cost
import ValidPartition
import KeptGraph
import KeptRun
import KeptParent
import KeptConsumers
import KeptControls
import LiteralControls
import Interfaces
import FreshReadout
import FreshConsumer
import FreshFalseTwins
import Lean
open Lean Elab Command
run_cmd do
  let env ← getEnv
  let wanted : List Name := [`RMAF, `Geometry, `Bridge, `Composition, `CoreGraph, `CherryCoarsening, `CoreProgram, `CoreInvariants, `SourceBridge, `Contraction, `Normalization, `InitialLift, `Suppression, `EraseLift, `Origins, `Branches, `CutRecords, `FullTransport, `Coverage, `Entrypoint, `OutputBudget, `ColorBudget, `ColorSteps, `RawMass, `RationalMass, `ParentColors, `OriginalGraph, `Display, `Regions, `History, `Realization, `OwnerCover, `CutCoverage, `InitialCoverage, `Cost, `ValidPartition, `KeptGraph, `KeptRun, `KeptParent, `KeptConsumers, `KeptControls, `LiteralControls, `Interfaces, `FreshReadout, `FreshConsumer, `FreshFalseTwins]
  let mut count : Nat := 0
  for (n,ci) in env.constants do
    if let some idx := env.getModuleIdxFor? n then
      let m := env.header.moduleNames[idx.toNat]!
      if wanted.contains m then
        match ci with
        | .thmInfo _ =>
          logInfo m!"PRINT_ORIGIN|{m}|{n}"
          elabCommand (← `(command| #print axioms $(mkIdent n)))
          count := count+1
        | _ => pure ()
  logInfo m!"PRINT_TOTAL|{count}"
