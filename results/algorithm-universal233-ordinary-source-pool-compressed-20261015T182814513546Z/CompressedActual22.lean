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
import GroupRestriction
import GroupEmbedding
import GroupPartition
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
import BothProgram
import Crossing
import Controls
import Rename
import GroupState
import GroupStateFacts
import GroupCost
import GroupForward
import GroupReconstruction
import GroupDefs
import GroupForwardProof
import GroupReverseProof
import GroupCostProof
import GroupPriority
import OutputDefs
import Materialize
import Equivalence
import CrossingCount
import Marked
import Clip
import Deletion
import MarkerSingleton
import MarkerBounds
import Port
import OriginalPort
import PortSingleton
import MixedPort
import CutHull
import ForestMerge
import MarkedLift
import StableMarker
import ClipCount
import Contract
import PortContract
import Projection
import OriginalSides
import OriginalProjection
import EdgeSides
import ProjectedPartition
import ProjectedForest
import MarkedProjection
import OriginalGlue
import HeadPermutation
import MarkerBlock
import MarkerNormal
import MergeStable
import CountOriginal
import MinimumIdentity
import DerivedMinimum
import GraphControls
import CallerDefs
import ChosenOwner
import LiteralNormal
import LiteralMerge
import PickMerge
import CallerSetup
import PaidDefs
import InsideBudget
import PaidExact
import ProperJobs
import LiteralExtension
import OutsideDefs
import OutsideExact
import CallerResources
import GuardedDefs
import GuardedExact
import CallerControls
import PaidControls
import OutsideControls
import GuardedControls
import GuardRefusalControls
import CallerFinal
import SourceDefs
import SourceControls
import SourceBoundary
import ActualCuts
import BuildSetup
import BuildComplete
import BuildIdentity
import SourceProgram
import OutsideOne
import ThreeOutside
import SourceNonrefusal
import BuilderControls
import ActualFrameControls
import SourceFinal
import ConsumerControls
import QueryCaller
import QuerySpecification
import QueryBudgets
import QueryMass
import QueryWork
import MafCaller
import LocalSlots
import Regional
import Indexing
import ForestColorWork
import ForestGeometryWork
import ForestDefs
import ForestPrecontrols
import ForestReplace
import ForestOverlap
import ForestReverse
import ForestProgram
import ForestSelection
import ForestProgramControls
import ForestConditional
import ForestQueries
import ForestLocal
import ForestDisjointPlan
import ForestDisjoint
import ForestWork
import ForestWorkBound
import ForestTrace
import ForestResource
import RecoveryProgram
import BlockColors
import Permutations
import Recovery
import FinalWork
import Rule4OriginalExchange
import Rule4PathPrune
import Rule4Graft
import Rule4SourceExchange
import Rule4Exchange
import Rule4LcaCoverage
import Rule4Cover
import Rule4LiteralCuts
import Rule4LiteralChecks
import Rule4Selector
import Rule4Costs
import Rule4Program
import Rule4Solve
import Rule4Controls
import CherryRemoval
import CherryForward
import CherryLeafClear
import CherryReverse
import CherryGraph
import CherryTopology
import CherryEndpoint
import CherryReplacement
import Ordinary
import Partition
import PoolClassificationSelector
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
import PoolClassificationControls
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
import LocalSelector
import ClassificationControls
import Case322Saving
import Case322Arcs
import Case322Partition
import Case322Cover
import Case322Caller
import Case322Controls
import Case322Instances
import RoleBinding
import BsideExtraction
import SourceOrientation
import OrientedSaving
import OrientedExchange
import OrientedBside
import CsideExtraction
import OrientedPathCover
import LiteralPlan
import CurrentPartition
import PlanCosts
import PathSpecification
import ExtractionControls
import ExtractionRootControls
import PaidPartitions
import PaidSelection
import PaidAncestor
import PaidRootBoundary
import PaidGuard
import PaidCaller
import PoolCase322PaidControls
import Lean
open Lean Elab Command
run_cmd do
  let env ← getEnv
  let wanted : List Name := [`Rule4LiteralCuts]
  let allowed : List Name := [`Classical.choice,`Quot.sound,`propext]
  let mut counts : Array Json := #[]
  let mut bad : Array Json := #[]
  for i in [:env.header.moduleNames.size] do
    let producer := env.header.moduleNames[i]!
    if wanted.contains producer then
      let data := env.header.moduleData[i]!
      unless data.constants.size == data.constNames.size do throwError "PRODUCER_ARRAY_LENGTH_MISMATCH"
      let mut rows : Array Json := #[]
      let filename := producer.toString ++ ".json.gz"
      counts := counts.push (Json.mkObj [("producer",toJson producer.toString),("count",toJson data.constants.size),("file",toJson filename)])
      for j in [:data.constants.size] do
        let ci := data.constants[j]!
        let stored := data.constNames[j]!
        unless stored == ci.name do throwError "PRODUCER_NAME_MISMATCH"
        let kind := match ci with
          | .axiomInfo _ => "axiom"
          | .defnInfo _ => "definition"
          | .thmInfo _ => "theorem"
          | .opaqueInfo _ => "opaque"
          | .quotInfo _ => "quotient"
          | .ctorInfo _ => "constructor"
          | .recInfo _ => "recursor"
          | .inductInfo _ => "inductive"
        let body := match ci with | .thmInfo _ => none | _ => ci.value? true
        let bodyText := match body with | some e => reprStr e | none => "<none>"
        let mut refs := ci.getUsedConstantsAsSet.toList
        if let some e := body then refs := refs ++ e.getUsedConstants.toList
        refs := refs.eraseDups
        let mut ax : List Name := []
        if ci.isAxiom then ax := [ci.name]
        for n in refs do ax := ax ++ (← collectAxioms n).toList
        ax := ax.eraseDups
        let resolved := match env.getModuleIdxFor? ci.name with
          | some k => env.header.moduleNames[k.toNat]!.toString
          | none => "<unresolved>"
        rows := rows.push (Json.mkObj [("producer",toJson producer.toString),("index",toJson j),
          ("stored_name",toJson stored.toString),("actual_name",toJson ci.name.toString),
          ("resolved_origin",toJson resolved),("kind",toJson kind),
          ("type",toJson (reprStr ci.type)),("body",toJson bodyText),("has_body",toJson (ci.value? true).isSome),("body_text_scope",toJson (match ci with | .thmInfo _ => "OMITTED_THEOREM_PROOF_TEXT" | _ => "FULL_NONPROOF_BODY")),
          ("direct_references",toJson (refs.map Name.toString)),("axiom_references",toJson (ax.map Name.toString))])
        if (ci.isAxiom && !allowed.contains ci.name) || ax.any (fun n => !allowed.contains n) then
          bad := bad.push (Json.mkObj [("producer",toJson producer.toString),("name",toJson ci.name.toString),("kind",toJson kind),("axioms",toJson (ax.map Name.toString))])
      let compressed ← liftIO <| IO.Process.output {cmd := "/bin/sh", args := #["-c", "exec /usr/bin/gzip -1 -c > /Users/paurel/Documents/ChatGPT/bootscience/results/algorithm-universal233-ordinary-source-pool-compressed-20261015T182814513546Z/records-Actual22/" ++ filename]} (some (Json.arr rows).pretty)
      unless compressed.exitCode == 0 do throwError "COMPRESSED_SINK_FAILED"
  liftIO <| IO.FS.writeFile ("/Users/paurel/Documents/ChatGPT/bootscience/results/algorithm-universal233-ordinary-source-pool-compressed-20261015T182814513546Z/records-Actual22" ++ "/index.json") (Json.mkObj [("producer_counts",Json.arr counts),("rejects",Json.arr bad)]).pretty
  if !bad.isEmpty then throwError m!"REJECT_PRODUCER_OCCURRENCE|{bad.size}"
  logInfo m!"PRODUCER_OCCURRENCE_PASS|{counts.size}"
