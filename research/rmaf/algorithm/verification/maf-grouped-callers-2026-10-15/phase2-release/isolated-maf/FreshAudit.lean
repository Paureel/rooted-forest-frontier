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
import Lean
open Lean Elab Command
run_cmd do
  let env ← getEnv
  let wanted : Array Name := #[`RMAF, `Geometry, `Bridge, `Composition, `CoreGraph, `CherryCoarsening, `CoreProgram, `CoreInvariants, `SourceBridge, `Contraction, `Normalization, `InitialLift, `Suppression, `EraseLift, `Origins, `Branches, `CutRecords, `OriginalGraph, `Display, `Regions, `History, `Realization, `OwnerCover, `Coverage, `InitialCoverage, `Cost, `ValidPartition, `Restriction, `Embedding, `Partition, `Pretest, `Controls, `Lemmas, `Reconstruction01, `Optimality01, `Witness01, `Runtime01, `ConsumerControls, `SourceColorControls, `RestrictionCost, `Forward, `Reconstruction, `QueryCaller, `QuerySpecification, `QueryBudgets, `QueryMass, `QueryWork, `MafCaller, `MafPrecontrols, `LocalSlots, `Regional, `Indexing, `OriginalReconstruction, `OriginalCaller, `OriginalPaid, `MafConsumerControls]
  let mut seen : Array Name := #[]
  for (n, info) in env.constants do
    if let some idx := env.getModuleIdxFor? n then
      let origin := env.header.moduleNames[idx.toNat]!
      if wanted.contains origin && !seen.contains n then
        seen := seen.push n
        let axioms ← collectAxioms n
        let kind := match info with
          | .axiomInfo _ => "axiom"
          | .thmInfo _ => "theorem"
          | _ => "other"
        logInfo m!"FRESH|{origin}|{n}|{kind}|{String.intercalate "," (axioms.toList.map toString)}"
  logInfo m!"FRESH_TOTAL|{seen.size}"
