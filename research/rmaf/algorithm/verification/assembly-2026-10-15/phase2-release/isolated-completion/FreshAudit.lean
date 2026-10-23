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
import Controls
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
import CutControls
import ParentColors
import WholeSource
import Requests
import OwnershipBase
import ChainAssembly
import SourceValidity
import ForestOutputs
import AssemblyControls
import Executable
import Endpoint
import Restriction
import PendantExclusion
import Refinement
import Components
import Safety
import WholeColors
import OriginalColors
import WholeMass
import MassControls
import PaidAssembly
import HardConsumer
import HardPaid
import CompletionControls
import Lean
open Lean Elab Command
run_cmd do
  let env ← getEnv
  let wanted : Array Name := #[`RMAF, `Geometry, `Bridge, `Composition, `CoreGraph, `CherryCoarsening, `CoreProgram, `CoreInvariants, `SourceBridge, `Contraction, `Normalization, `InitialLift, `Suppression, `EraseLift, `Origins, `Branches, `CutRecords, `FullTransport, `Coverage, `Entrypoint, `OutputBudget, `ColorBudget, `ColorSteps, `RawMass, `RationalMass, `Controls, `OriginalGraph, `Display, `Regions, `History, `Realization, `OwnerCover, `CutCoverage, `InitialCoverage, `Cost, `ValidPartition, `CutControls, `ParentColors, `WholeSource, `Requests, `OwnershipBase, `ChainAssembly, `SourceValidity, `ForestOutputs, `AssemblyControls, `Executable, `Endpoint, `Restriction, `PendantExclusion, `Refinement, `Components, `Safety, `WholeColors, `OriginalColors, `WholeMass, `MassControls, `PaidAssembly, `HardConsumer, `HardPaid, `CompletionControls]
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
