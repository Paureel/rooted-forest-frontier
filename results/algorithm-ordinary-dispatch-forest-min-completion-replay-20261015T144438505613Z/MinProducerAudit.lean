import RMAF
import GroupRestriction
import GroupEmbedding
import GroupPartition
import GroupCost
import GroupForward
import Geometry
import Bridge
import Composition
import GroupReconstruction
import GroupState
import GroupStateFacts
import GroupDefs
import GroupForwardProof
import GroupReverseProof
import GroupCostProof
import GroupPriority
import CoreGraph
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
import WholeColors
import OriginalColors
import WholeMass
import Pretest
import Lemmas
import Reconstruction01
import Optimality01
import Witness01
import OutputDefs
import Materialize
import Equivalence
import QueryCaller
import QuerySpecification
import QueryBudgets
import QueryMass
import QueryWork
import ForestDefs
import ForestPrecontrols
import ForestReplace
import ForestOverlap
import ForestReverse
import ForestProgram
import MinPrecontrols
import ForestMinimumCompletion
import MinimumCompletionControls
import Lean
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Lean Elab Command
run_cmd do
 let env ← getEnv
 let expected : List Name := [`RMAF, `GroupRestriction, `GroupEmbedding, `GroupPartition, `GroupCost, `GroupForward, `Geometry, `Bridge, `Composition, `GroupReconstruction, `GroupState, `GroupStateFacts, `GroupDefs, `GroupForwardProof, `GroupReverseProof, `GroupCostProof, `GroupPriority, `CoreGraph, `SourceBridge, `CherryCoarsening, `CoreProgram, `CoreInvariants, `Contraction, `Normalization, `InitialLift, `Suppression, `EraseLift, `Origins, `Branches, `CutRecords, `FullTransport, `Coverage, `Entrypoint, `OutputBudget, `ColorBudget, `ColorSteps, `RawMass, `RationalMass, `ParentColors, `OriginalGraph, `Display, `Regions, `History, `Realization, `OwnerCover, `CutCoverage, `InitialCoverage, `Cost, `ValidPartition, `WholeSource, `Requests, `OwnershipBase, `ChainAssembly, `SourceValidity, `WholeColors, `OriginalColors, `WholeMass, `Pretest, `Lemmas, `Reconstruction01, `Optimality01, `Witness01, `OutputDefs, `Materialize, `Equivalence, `QueryCaller, `QuerySpecification, `QueryBudgets, `QueryMass, `QueryWork, `ForestDefs, `ForestPrecontrols, `ForestReplace, `ForestOverlap, `ForestReverse, `ForestProgram, `MinPrecontrols, `ForestMinimumCompletion, `MinimumCompletionControls]
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
