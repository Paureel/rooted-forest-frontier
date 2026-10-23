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
import OriginalGraph
import Display
import Regions
import History
import Realization
import OwnerCover
import Coverage
import InitialCoverage
import Cost
import ValidPartition
import Restriction
import Embedding
import Partition
import Pretest
import Controls
import Lemmas
import Reconstruction01
import Optimality01
import Witness01
import Runtime01
import ConsumerControls
import SourceColorControls
import RestrictionCost
import Forward
import Reconstruction
import QueryCaller
import QuerySpecification
import QueryBudgets
import QueryMass
import QueryWork
import MafCaller
import MafPrecontrols
import LocalSlots
import Regional
import Indexing
import OriginalReconstruction
import OriginalCaller
import OriginalPaid
import MafConsumerControls
import PlantPrivate
import Lean
open Lean Elab Command
run_cmd do
 let env ← getEnv
 let mods : List Name := [`RMAF, `Geometry, `Bridge, `Composition, `CoreGraph, `CherryCoarsening, `CoreProgram, `CoreInvariants, `SourceBridge, `Contraction, `Normalization, `InitialLift, `Suppression, `EraseLift, `Origins, `Branches, `CutRecords, `OriginalGraph, `Display, `Regions, `History, `Realization, `OwnerCover, `Coverage, `InitialCoverage, `Cost, `ValidPartition, `Restriction, `Embedding, `Partition, `Pretest, `Controls, `Lemmas, `Reconstruction01, `Optimality01, `Witness01, `Runtime01, `ConsumerControls, `SourceColorControls, `RestrictionCost, `Forward, `Reconstruction, `QueryCaller, `QuerySpecification, `QueryBudgets, `QueryMass, `QueryWork, `MafCaller, `MafPrecontrols, `LocalSlots, `Regional, `Indexing, `OriginalReconstruction, `OriginalCaller, `OriginalPaid, `MafConsumerControls, `PlantPrivate]
 let ns := (((env.constants.map₁.toList ++ env.constants.map₂.toList).map (·.1)).filter fun n =>
   match env.getModuleIdxFor? n with
   | some i => mods.contains env.header.moduleNames[i.toNat]!
   | none => false).eraseDups
 for n in ns do
   let some i := env.getModuleIdxFor? n | throwError "missing module"
   logInfo m!"MODULE|{env.header.moduleNames[i.toNat]!}|{n}"
   let axs ← collectAxioms n
   logInfo m!"MODAUDIT|{n}|{axs.toList}"
   for ax in axs do
    unless ax == `propext || ax == `Quot.sound || ax == `Classical.choice do
      throwError m!"REJECT_CUSTOM_AXIOM|{n}|{ax}"
