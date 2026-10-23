import RMAF
import CoreGraph
import Geometry
import Bridge
import Composition
import SourceBridge
import CherryCoarsening
import CoreProgram
import CoreInvariants
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
import WholeSource
import Requests
import OwnershipBase
import ChainAssembly
import SourceValidity
import ForestOutputs
import WholeColors
import OriginalColors
import WholeMass
import PaidAssembly
import Executable
import Endpoint
import Restriction
import PendantExclusion
import Refinement
import Components
import Safety
import HardConsumer
import HardPaid
import HardForest
import Selector
import ExchangeRestriction
import Cluster
import Descendant
import Forest
import Surgery
import Count
import Parents
import Exchange
import SourceEdge
import Interface
import SideColors
import PairConsumer
import VertexPair
import GoodPair
import RankCost
import MinimumUnique
import TailMass
import ColorClasses
import Probe
import Work
import ProbeWork
import FourProbe
import KeptGraph
import KeptRun
import KeptParent
import KeptConsumers
import Pretest
import DepthRestriction
import Embedding
import Partition
import Lemmas
import Reconstruction01
import Optimality01
import Witness01
import LiteralControls
import BinaryEdge
import CheapPartition
import TargetGeometry
import Continuation
import LocalOne
import PretestConsumer
import SelectedContinuation
import Symmetry
import SelectedHigh
import ConsumerControls
import PlantPrivate
import Lean
open Lean Elab Command
run_cmd do
 let env ← getEnv
 let mods : List Name := [`RMAF, `CoreGraph, `Geometry, `Bridge, `Composition, `SourceBridge, `CherryCoarsening, `CoreProgram, `CoreInvariants, `Contraction, `Normalization, `InitialLift, `Suppression, `EraseLift, `Origins, `Branches, `CutRecords, `FullTransport, `Coverage, `Entrypoint, `OutputBudget, `ColorBudget, `ColorSteps, `RawMass, `RationalMass, `ParentColors, `OriginalGraph, `Display, `Regions, `History, `Realization, `OwnerCover, `CutCoverage, `InitialCoverage, `Cost, `ValidPartition, `WholeSource, `Requests, `OwnershipBase, `ChainAssembly, `SourceValidity, `ForestOutputs, `WholeColors, `OriginalColors, `WholeMass, `PaidAssembly, `Executable, `Endpoint, `Restriction, `PendantExclusion, `Refinement, `Components, `Safety, `HardConsumer, `HardPaid, `HardForest, `Selector, `ExchangeRestriction, `Cluster, `Descendant, `Forest, `Surgery, `Count, `Parents, `Exchange, `SourceEdge, `Interface, `SideColors, `PairConsumer, `VertexPair, `GoodPair, `RankCost, `MinimumUnique, `TailMass, `ColorClasses, `Probe, `Work, `ProbeWork, `FourProbe, `KeptGraph, `KeptRun, `KeptParent, `KeptConsumers, `Pretest, `DepthRestriction, `Embedding, `Partition, `Lemmas, `Reconstruction01, `Optimality01, `Witness01, `LiteralControls, `BinaryEdge, `CheapPartition, `TargetGeometry, `Continuation, `LocalOne, `PretestConsumer, `SelectedContinuation, `Symmetry, `SelectedHigh, `ConsumerControls, `PlantPrivate]
 let ns := (((env.constants.map₁.toList ++ env.constants.map₂.toList).map (·.1)).filter fun n =>
   match env.getModuleIdxFor? n with
   | some i => mods.contains env.header.moduleNames[i.toNat]!
   | none => false).eraseDups
 for n in ns do
   let some i := env.getModuleIdxFor? n | throwError "missing module origin"
   logInfo m!"MODULE|{env.header.moduleNames[i.toNat]!}|{n}"
   let axs ← collectAxioms n
   logInfo m!"MODAUDIT|{n}|{axs.toList}"
   for ax in axs do
    unless ax == `propext || ax == `Quot.sound || ax == `Classical.choice do
      throwError m!"REJECT_CUSTOM_AXIOM|{n}|{ax}"
