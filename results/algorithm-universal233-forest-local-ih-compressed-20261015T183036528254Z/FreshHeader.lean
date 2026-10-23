import RMAF
import GroupRestriction
import GroupEmbedding
import GroupPartition
import GroupState
import GroupStateFacts
import GroupCost
import GroupForward
import Geometry
import Bridge
import Composition
import GroupReconstruction
import GroupDefs
import GroupForwardProof
import GroupReverseProof
import GroupCostProof
import GroupPriority
import OutputDefs
import Materialize
import Equivalence
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
import WholeColors
import OriginalColors
import WholeMass
import QueryCaller
import QuerySpecification
import QueryBudgets
import QueryMass
import QueryWork
import Pretest
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
import Lemmas
import Reconstruction01
import Optimality01
import Witness01
import ForestDefs
import ForestPrecontrols
import ParentColors
import WholeSource
import Requests
import OwnershipBase
import ChainAssembly
import SourceValidity
import ForestReplace
import ForestOverlap
import ForestReverse
import ForestProgram
import ForestSelection
import ForestConditional
import ForestQueries
import MafCaller
import LocalSlots
import Regional
import Indexing
import ForestLocal
import ForestDisjointPlan
import ForestDisjoint
import LocalCongruence
import ForestMinimumCompletion
import LocalExact
import ForestProgramControls
import LocalControls
import TransferControls
import Lean
open Lean Elab Command
run_cmd do
 let env ← getEnv
 let wanted : List Name := [`RMAF, `GroupRestriction, `GroupEmbedding, `GroupPartition, `GroupState, `GroupStateFacts, `GroupCost, `GroupForward, `Geometry, `Bridge, `Composition, `GroupReconstruction, `GroupDefs, `GroupForwardProof, `GroupReverseProof, `GroupCostProof, `GroupPriority, `OutputDefs, `Materialize, `Equivalence, `CoreGraph, `SourceBridge, `CherryCoarsening, `CoreProgram, `CoreInvariants, `Contraction, `Normalization, `InitialLift, `Suppression, `EraseLift, `Origins, `Branches, `CutRecords, `FullTransport, `Coverage, `Entrypoint, `OutputBudget, `ColorBudget, `ColorSteps, `RawMass, `RationalMass, `WholeColors, `OriginalColors, `WholeMass, `QueryCaller, `QuerySpecification, `QueryBudgets, `QueryMass, `QueryWork, `Pretest, `OriginalGraph, `Display, `Regions, `History, `Realization, `OwnerCover, `CutCoverage, `InitialCoverage, `Cost, `ValidPartition, `Lemmas, `Reconstruction01, `Optimality01, `Witness01, `ForestDefs, `ForestPrecontrols, `ParentColors, `WholeSource, `Requests, `OwnershipBase, `ChainAssembly, `SourceValidity, `ForestReplace, `ForestOverlap, `ForestReverse, `ForestProgram, `ForestSelection, `ForestConditional, `ForestQueries, `MafCaller, `LocalSlots, `Regional, `Indexing, `ForestLocal, `ForestDisjointPlan, `ForestDisjoint, `LocalCongruence, `ForestMinimumCompletion, `LocalExact, `ForestProgramControls, `LocalControls, `TransferControls]
 for i in [:env.header.moduleNames.size] do
  let producer := env.header.moduleNames[i]!
  let path ← liftIO <| findOLean producer
  logInfo m!"PATH|{producer}|{path}"
  if wanted.contains producer then
   let data := env.header.moduleData[i]!
   unless data.constants.size == data.constNames.size do throwError "HEADER_ARRAY_MISMATCH"
   logInfo m!"COUNT|{producer}|{data.constants.size}"
   for j in [:data.constants.size] do
    let ci := data.constants[j]!
    let kind := match ci with
      | .axiomInfo _ => "axiom" | .defnInfo _ => "definition" | .thmInfo _ => "theorem"
      | .opaqueInfo _ => "opaque" | .quotInfo _ => "quotient" | .ctorInfo _ => "constructor"
      | .recInfo _ => "recursor" | .inductInfo _ => "inductive"
    logInfo m!"NAME|{producer}|{j}|{ci.name}|{kind}"
