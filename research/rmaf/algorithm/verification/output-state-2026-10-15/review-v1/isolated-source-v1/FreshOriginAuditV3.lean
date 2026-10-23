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
import OutputDefs
import OutputControls
import Materialize
import Equivalence
import Permutation
import OppositeGroups
import LocalCertificates
import ResidualConsumer
import ActualConsumers
import FreshActualReadoutsV2
import FreshEveryOutputConsumerV1
import FreshActualCleanV1
import Lean
open Lean Elab Command
set_option maxRecDepth 100000
set_option maxHeartbeats 12000000
run_cmd do
 let env ← getEnv
 let modules : List Name := [`RMAF,`GroupRestriction,`GroupEmbedding,`GroupPartition,`GroupCost,`GroupForward,`Geometry,`Bridge,`Composition,`GroupReconstruction,`GroupState,`GroupStateFacts,`GroupDefs,`GroupForwardProof,`GroupReverseProof,`GroupCostProof,`GroupPriority,`CoreGraph,`SourceBridge,`CherryCoarsening,`CoreProgram,`CoreInvariants,`Contraction,`Normalization,`InitialLift,`Suppression,`EraseLift,`Origins,`Branches,`CutRecords,`FullTransport,`Coverage,`Entrypoint,`OutputBudget,`ColorBudget,`ColorSteps,`RawMass,`RationalMass,`ParentColors,`OriginalGraph,`Display,`Regions,`History,`Realization,`OwnerCover,`CutCoverage,`InitialCoverage,`Cost,`ValidPartition,`WholeSource,`Requests,`OwnershipBase,`ChainAssembly,`SourceValidity,`ForestOutputs,`WholeColors,`OriginalColors,`WholeMass,`PaidAssembly,`Executable,`Endpoint,`Restriction,`PendantExclusion,`Refinement,`Components,`Safety,`HardConsumer,`HardPaid,`HardForest,`Selector,`ExchangeRestriction,`Cluster,`Descendant,`Forest,`Surgery,`Count,`Parents,`Exchange,`SourceEdge,`Interface,`SideColors,`PairConsumer,`VertexPair,`GoodPair,`RankCost,`MinimumUnique,`TailMass,`ColorClasses,`Probe,`Work,`ProbeWork,`FourProbe,`KeptGraph,`KeptRun,`KeptParent,`KeptConsumers,`Pretest,`Lemmas,`Reconstruction01,`Optimality01,`Witness01,`LiteralControls,`BinaryEdge,`CheapPartition,`TargetGeometry,`Continuation,`LocalOne,`PretestConsumer,`SelectedContinuation,`Symmetry,`SelectedHigh,`ConsumerControls,`OutputDefs,`OutputControls,`Materialize,`Equivalence,`Permutation,`OppositeGroups,`LocalCertificates,`ResidualConsumer,`ActualConsumers,`FreshActualReadoutsV2,`FreshEveryOutputConsumerV1,`FreshActualCleanV1]
 let allowed : List Name := [`propext, `Classical.choice, `Quot.sound]
 let mut seen : List Name := []
 let mut bad : Nat := 0
 for origin in modules do
  let p ← liftIO <| findOLean origin
  logInfo m!"PATH|{origin}|{p}"
 for (n,i) in env.constants.toList do
  if let some idx := env.getModuleIdxFor? n then
   let origin := env.allImportedModuleNames[idx.toNat]!
   if modules.contains origin then
    seen := origin :: seen
    let axs ← collectAxioms n
    let reject := i.isAxiom || i.isUnsafe || axs.toList.any (fun a => !allowed.contains a)
    if reject then bad := bad+1
    let kind := match i with
      | .axiomInfo _ => "axiom" | .defnInfo _ => "definition" | .thmInfo _ => "theorem"
      | .opaqueInfo _ => "opaque" | .quotInfo _ => "quotient" | .inductInfo _ => "inductive"
      | .ctorInfo _ => "constructor" | .recInfo _ => "recursor"
    let bodyHash := match i.value? with | none => "none" | some v => toString (hash v)
    let obj := Json.mkObj [
      ("origin",toJson origin.toString),("name",toJson n.toString),("kind",toJson kind),
      ("axioms",toJson (axs.toList.map Name.toString)),("is_axiom",toJson i.isAxiom),
      ("unsafe",toJson i.isUnsafe),("rejected",toJson reject),
      ("type_expr",toJson (reprStr i.type)),("type_structural_hash64",toJson (toString (hash i.type))),
      ("body_structural_hash64",toJson bodyHash)]
    logInfo m!"DECLJSON|{obj.compress}"
 for origin in modules do
  let count := (seen.filter (· == origin)).length
  logInfo m!"COUNT|{origin}|{count}"
  if count == 0 then throwError "FRESH_MISSING_ORIGIN"
 logInfo m!"BAD|{bad}"
 if bad > 0 then throwError "FRESH_FORBIDDEN_ORIGIN_DECLARATION"
