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
      let compressed ← liftIO <| IO.Process.output {cmd := "/bin/sh", args := #["-c", "exec /usr/bin/gzip -1 -c > /Users/paurel/Documents/ChatGPT/bootscience/results/algorithm-universal233-forest-local-ih-compressed-20261015T183036528254Z/records-LocalIHAll/" ++ filename]} (some (Json.arr rows).pretty)
      unless compressed.exitCode == 0 do throwError "COMPRESSED_SINK_FAILED"
  liftIO <| IO.FS.writeFile ("/Users/paurel/Documents/ChatGPT/bootscience/results/algorithm-universal233-forest-local-ih-compressed-20261015T183036528254Z/records-LocalIHAll" ++ "/index.json") (Json.mkObj [("producer_counts",Json.arr counts),("rejects",Json.arr bad)]).pretty
  if !bad.isEmpty then throwError m!"REJECT_PRODUCER_OCCURRENCE|{bad.size}"
  logInfo m!"PRODUCER_OCCURRENCE_PASS|{counts.size}"
