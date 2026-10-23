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
import Rule5Defs
import Rule5PreControls
import Rule5Graph
import Rule5Triples
import Rule5Exchange
import Rule5Case323
import Rule5Case321
import Rule5GraphControls
import Attachment
import AdmittedGeometry
import UniqueCherry
import FiveBranches
import AdmittedCases
import OutsideCore
import LargePendant
import LargeExchange
import LargeAdmitted
import SourceWork
import ClassificationControls
import Lean
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Lean Elab Command
run_cmd do
 let env ← getEnv
 let expected : List Name := [`RMAF, `Geometry, `Bridge, `Composition, `CoreGraph, `CherryCoarsening, `CoreProgram, `CoreInvariants, `SourceBridge, `Contraction, `Normalization, `InitialLift, `Suppression, `EraseLift, `Origins, `Branches, `CutRecords, `OriginalGraph, `Executable, `Endpoint, `Restriction, `PendantExclusion, `Refinement, `Components, `Safety, `GroupRestriction, `GroupEmbedding, `GroupPartition, `GroupCost, `GroupForward, `GroupReconstruction, `GroupState, `GroupStateFacts, `GroupDefs, `GroupForwardProof, `GroupReverseProof, `GroupCostProof, `GroupPriority, `OutputDefs, `Materialize, `Equivalence, `CherryRemoval, `CherryForward, `CherryLeafClear, `CherryReverse, `CherryGraph, `CherryTopology, `CherryEndpoint, `CherryReplacement, `ExchangeRestriction, `Cluster, `Descendant, `Forest, `Surgery, `Count, `Ordinary, `Partition, `Selector, `Endpoints, `Consumer, `Priority, `SourceBranches, `CoreCherry, `PreControls, `T1Split, `T1Exchange, `T1Boundary, `Budget, `Unordered, `Controls, `Rule5Defs, `Rule5PreControls, `Rule5Graph, `Rule5Triples, `Rule5Exchange, `Rule5Case323, `Rule5Case321, `Rule5GraphControls, `Attachment, `AdmittedGeometry, `UniqueCherry, `FiveBranches, `AdmittedCases, `OutsideCore, `LargePendant, `LargeExchange, `LargeAdmitted, `SourceWork, `ClassificationControls]
 for i in [:env.header.moduleNames.size] do
   let producer := env.header.moduleNames[i]!
   let path ← liftIO <| findOLean producer
   logInfo m!"PATH|{producer}|{path}"
   if expected.contains producer then
     let data := env.header.moduleData[i]!
     unless data.constants.size == data.constNames.size do
       throwError m!"PRODUCER_NAME_LENGTH_MISMATCH|{producer}"
     logInfo m!"SUMMARY|{producer}|{data.constants.size}"
     for j in [:data.constants.size] do
       let ci := data.constants[j]!
       unless data.constNames[j]! == ci.name do
         throwError m!"PRODUCER_NAME_ROW_MISMATCH|{producer}|{j}"
       let kind := match ci with
         | .axiomInfo _ => "axiom"
         | .defnInfo _ => "definition"
         | .thmInfo _ => "theorem"
         | .opaqueInfo _ => "opaque"
         | .quotInfo _ => "quotient"
         | .inductInfo _ => "inductive"
         | .ctorInfo _ => "constructor"
         | .recInfo _ => "recursor"
       let resolved := match env.getModuleIdxFor? ci.name with
         | none => "UNATTRIBUTED"
         | some idx => toString env.header.moduleNames[idx.toNat]!
       if resolved == "UNATTRIBUTED" then
         throwError m!"UNATTRIBUTED_PRODUCER|{producer}|{ci.name}"
       let refs := ci.getUsedConstantsAsSet.toList
       let mut axs : List Name := []
       for dep in refs do
         let da ← collectAxioms dep
         axs := (axs ++ da.toList).eraseDups
       let row := Json.mkObj [
         ("producer",toJson (toString producer)),("index",toJson j),
         ("name",toJson (toString ci.name)),("resolved_origin",toJson resolved),
         ("kind",toJson kind),("type",toJson (reprStr ci.type)),
         ("body",toJson (ci.value?.map reprStr)),
         ("references",toJson (refs.map toString)),
         ("axiom_references",toJson (axs.map toString))]
       logInfo m!"PRODUCERJSON|{row.compress}"
       if kind == "axiom" then
         unless ci.name == `Classical.choice || ci.name == `propext || ci.name == `Quot.sound do
           throwError m!"REJECT_DIRECT_CUSTOM_AXIOM|{producer}|{j}|{ci.name}"
       for ax in axs do
         unless ax == `Classical.choice || ax == `propext || ax == `Quot.sound do
           throwError m!"REJECT_DEPENDENCY_CUSTOM_AXIOM|{producer}|{j}|{ci.name}|{ax}"
