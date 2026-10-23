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
import Executable
import Endpoint
import Restriction
import PendantExclusion
import Refinement
import Components
import Safety
import GroupRestriction
import GroupEmbedding
import GroupPartition
import GroupCost
import GroupForward
import GroupReconstruction
import GroupState
import GroupStateFacts
import GroupDefs
import GroupForwardProof
import GroupReverseProof
import GroupCostProof
import GroupPriority
import OutputDefs
import Materialize
import Equivalence
import CherryRemoval
import CherryForward
import CherryLeafClear
import CherryReverse
import CherryGraph
import CherryTopology
import CherryEndpoint
import CherryReplacement
import ExchangeRestriction
import Cluster
import Descendant
import Forest
import Surgery
import Count
import Ordinary
import Partition
import Selector
import Endpoints
import Consumer
import Priority
import SourceBranches
import CoreCherry
import PreControls
import T1Split
import T1Exchange
import T1Boundary
import Budget
import Unordered
import Controls
import Lean
open Lean Elab Command
run_cmd do
 let env ← getEnv
 let mods : List Name := [`RMAF, `Geometry, `Bridge, `Composition, `CoreGraph, `CherryCoarsening, `CoreProgram, `CoreInvariants, `SourceBridge, `Contraction, `Normalization, `InitialLift, `Suppression, `EraseLift, `Origins, `Branches, `CutRecords, `OriginalGraph, `Executable, `Endpoint, `Restriction, `PendantExclusion, `Refinement, `Components, `Safety, `GroupRestriction, `GroupEmbedding, `GroupPartition, `GroupCost, `GroupForward, `GroupReconstruction, `GroupState, `GroupStateFacts, `GroupDefs, `GroupForwardProof, `GroupReverseProof, `GroupCostProof, `GroupPriority, `OutputDefs, `Materialize, `Equivalence, `CherryRemoval, `CherryForward, `CherryLeafClear, `CherryReverse, `CherryGraph, `CherryTopology, `CherryEndpoint, `CherryReplacement, `ExchangeRestriction, `Cluster, `Descendant, `Forest, `Surgery, `Count, `Ordinary, `Partition, `Selector, `Endpoints, `Consumer, `Priority, `SourceBranches, `CoreCherry, `PreControls, `T1Split, `T1Exchange, `T1Boundary, `Budget, `Unordered, `Controls]
 for mod in env.header.moduleNames do
   let path ← liftIO <| findOLean mod
   logInfo m!"PATH|{mod}|{path}"
 let ns := (((env.constants.map₁.toList ++ env.constants.map₂.toList).map (·.1)).filter fun n =>
   match env.getModuleIdxFor? n with
   | some i => mods.contains env.header.moduleNames[i.toNat]!
   | none => false).eraseDups
 for n in ns do
   let some i := env.getModuleIdxFor? n | throwError "missing module origin"
   logInfo m!"MODULE|{env.header.moduleNames[i.toNat]!}|{n}"
   let axs ← collectAxioms n
   logInfo m!"MODAUDIT|{n}|{String.intercalate "," (axs.toList.map toString)}"
   for a in axs do
     unless a == `propext || a == `Quot.sound || a == `Classical.choice do
       throwError m!"REJECT_CUSTOM_AXIOM|{n}|{a}"
