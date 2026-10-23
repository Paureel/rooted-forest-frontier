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
import RankCost
import MinimumUnique
import TailMass
import ColorClasses
import Regression
import RankControls
import Work
import Primitive
import Payload
import CoreWorkControls
import RecoveryProgram
import BlockColors
import Permutations
import Recovery
import FinalWork
import FinalRecoveryControls
import FinalRegression
import StateRestriction
import StateEmbedding
import StatePartition
import StateCost
import State
import PreControls
import ColorDP
import ColorRegions
import ActualProgram
import TargetEmbedding
import IsoTransport
import StateSoundness
import CutColoring
import LowerBound
import ExactMinimum
import DPControls
import ConsumerControls
import PlantModel
import Lean
open Lean Elab Command
run_cmd do
  let env ← getEnv
  let modules : List Name := [`RMAF, `Geometry, `Bridge, `Composition, `CoreGraph, `CherryCoarsening, `CoreProgram, `CoreInvariants, `SourceBridge, `Contraction, `Normalization, `InitialLift, `Suppression, `EraseLift, `Origins, `Branches, `CutRecords, `FullTransport, `Coverage, `Entrypoint, `OutputBudget, `ColorBudget, `ColorSteps, `RawMass, `RationalMass, `Controls, `OriginalGraph, `Display, `Regions, `History, `Realization, `OwnerCover, `CutCoverage, `InitialCoverage, `Cost, `ValidPartition, `CutControls, `ParentColors, `WholeSource, `Requests, `OwnershipBase, `ChainAssembly, `SourceValidity, `ForestOutputs, `AssemblyControls, `RankCost, `MinimumUnique, `TailMass, `ColorClasses, `Regression, `RankControls, `Work, `Primitive, `Payload, `CoreWorkControls, `RecoveryProgram, `BlockColors, `Permutations, `Recovery, `FinalWork, `FinalRecoveryControls, `FinalRegression, `StateRestriction, `StateEmbedding, `StatePartition, `StateCost, `State, `PreControls, `ColorDP, `ColorRegions, `ActualProgram, `TargetEmbedding, `IsoTransport, `StateSoundness, `CutColoring, `LowerBound, `ExactMinimum, `DPControls, `ConsumerControls, `PlantModel]
  for mod in env.header.moduleNames do
    let path ← liftIO <| findOLean mod
    logInfo m!"PATH|{mod}|{path}"
  let ns := (env.constants.map₁.toList ++ env.constants.map₂.toList).map (·.1)
  let ns := (ns.filter fun n =>
    match env.getModuleIdxFor? n with
    | some idx => modules.contains env.header.moduleNames[idx.toNat]!
    | none => false).eraseDups
  for n in ns do
    let some idx := env.getModuleIdxFor? n | throwError "missing module origin"
    let mod := env.header.moduleNames[idx.toNat]!
    logInfo m!"MODULE|{mod}|{n}"
  for n in ns do
    let axs ← collectAxioms n
    logInfo m!"MODAUDIT|{n}|{String.intercalate "," (axs.toList.map toString)}"
    for a in axs do
      unless a == `propext || a == `Quot.sound || a == `Classical.choice do
        throwError m!"REJECT_CUSTOM_AXIOM|{n}|{a}"
