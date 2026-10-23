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
import Lean
open Lean Elab Command
run_cmd do
  let env ← getEnv
  let wanted : Array Name := #[`RMAF, `Geometry, `Bridge, `Composition, `CoreGraph, `CherryCoarsening, `CoreProgram, `CoreInvariants, `SourceBridge, `Contraction, `Normalization, `InitialLift, `Suppression, `EraseLift, `Origins, `Branches, `CutRecords, `FullTransport, `Coverage, `Entrypoint, `OutputBudget, `ColorBudget, `ColorSteps, `RawMass, `RationalMass, `ParentColors, `OriginalGraph, `Display, `Regions, `History, `Realization, `OwnerCover, `CutCoverage, `InitialCoverage, `Cost, `ValidPartition, `KeptGraph, `KeptRun, `KeptParent, `KeptConsumers, `KeptControls, `LiteralControls, `Interfaces]
  let mut seen : Array Name := #[]
  for (n, info) in env.constants do
    if let some idx := env.getModuleIdxFor? n then
      let origin := env.header.moduleNames[idx.toNat]!
      if wanted.contains origin && !seen.contains n then
        seen := seen.push n
        let axioms ← collectAxioms n
        let kind := match info with
          | .axiomInfo _ => "axiom"
          | .thmInfo _ => "theorem"
          | _ => "other"
        logInfo m!"FRESH|{origin}|{n}|{kind}|{String.intercalate "," (axioms.toList.map toString)}"
  logInfo m!"FRESH_TOTAL|{seen.size}"
