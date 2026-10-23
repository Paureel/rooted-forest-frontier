import QueryCaller
import QuerySpecification
import QueryBudgets
import QueryMass
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
import ForestPretest01
import ForestPermutation
import ForestCoverage
import ForestPretestSemantics
import CurrentQuery
import FullStateJobs
import FullStateSchedule
import GroupedExact
import ForestOutputs
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
import LiteralControls
import BinaryEdge
import CheapPartition
import TargetGeometry
import Continuation
import LocalOne
import PretestConsumer
import SelectedContinuation
import Permutation
import OppositeGroups
import ABCBinding
import BadGroups
import GroupInterface
import ColorDP
import ColorRegions
import ActualProgram
import TargetEmbedding
import IsoTransport
import StateSoundness
import CutColoring
import RecoveryProgram
import BlockColors
import Permutations
import Recovery
import LowerBound
import ExactMinimum
import Ordinary
import Partition
import PoolClassificationSelector
import Endpoints
import Consumer
import Priority
import SourceBranches
import CoreCherry
import CherryRemoval
import CherryForward
import CherryLeafClear
import CherryReverse
import CherryGraph
import CherryTopology
import CherryEndpoint
import CherryReplacement
import T1Split
import T1Exchange
import T1Boundary
import Budget
import Unordered
import Rule5Defs
import Rule5PreControls
import Rule5Graph
import Rule5Triples
import Rule5Exchange
import Rule5Case323
import Rule5Case321
import Case322Saving
import Case322Arcs
import Case322Partition
import Case322Cover
import Case322Caller
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
import PaidPartitions
import PaidSelection
import PaidAncestor
import PaidRootBoundary
import PaidGuard
import PaidCaller
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
import RemainingStatus
import IncidentClassification
import FinalSelector
import SourceSpine
import FinalInterface
import SelectorGeometry
import SelectorBuilder
import SelectorConsumer
import PaidRequests
import BoundedRequests
import SelectedExact
import TwoGroupDP
import TwoGroupComplete
import ActualPair
import Symmetry
import SelectedHigh
import BothProgram
import Crossing
import CoreCover
import Planner
import PlannerFacts
import PlannerSources
import OriginalReconstruction
import OriginalCaller
import OriginalPaid
import LocalCertificates
import ResidualConsumer
import Dispatcher
import BothPrecontrols
import PlannerControls
import DispatchControls
import ExecutionFacts
import ForestContract
import OrdinaryBridge
import RetainedBridge
import RetainedLower
import PlannerGeometry
import CheapPlannerCover
import PlanCover
import QueryTrace
import ActualBadSlots
import MassAssembly
import PairExecution
import PairExact
import PairControls
import Lean
open Lean Elab Command
run_cmd do
  let env ← getEnv
  let wanted : List Name := [`TwoGroupDP, `TwoGroupComplete, `ActualPair, `PairExecution, `PairExact, `PairControls]
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
      let compressed ← liftIO <| IO.Process.output {cmd := "/bin/sh", args := #["-c", "exec /usr/bin/gzip -1 -c > /Users/paurel/Documents/ChatGPT/bootscience/results/algorithm-universal233-pair-allgood-query-audit-20261015T201436963628Z/records-CaseNew/" ++ filename]} (some (Json.arr rows).pretty)
      unless compressed.exitCode == 0 do throwError "COMPRESSED_SINK_FAILED"
  liftIO <| IO.FS.writeFile ("/Users/paurel/Documents/ChatGPT/bootscience/results/algorithm-universal233-pair-allgood-query-audit-20261015T201436963628Z/records-CaseNew" ++ "/index.json") (Json.mkObj [("producer_counts",Json.arr counts),("rejects",Json.arr bad)]).pretty
  if !bad.isEmpty then throwError m!"REJECT_PRODUCER_OCCURRENCE|{bad.size}"
  logInfo m!"PRODUCER_OCCURRENCE_PASS|{counts.size}"
