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
import PretestSlotsV2
import Lean
open Lean Elab Command
run_cmd do
  let env ← getEnv
  let modules : List Name := [`RMAF,`Geometry,`Bridge,`Composition,`CoreGraph,`CherryCoarsening,`CoreProgram,`CoreInvariants,`SourceBridge,`Contraction,`Normalization,`InitialLift,`Suppression,`EraseLift,`Origins,`Branches,`CutRecords,`OriginalGraph,`Display,`Regions,`History,`Realization,`OwnerCover,`Coverage,`InitialCoverage,`Cost,`ValidPartition,`Restriction,`Embedding,`Partition,`Pretest,`Controls,`Lemmas,`Reconstruction01,`Optimality01,`Witness01,`Runtime01,`ConsumerControls,`SourceColorControls,`PretestSlotsV2]
  if modules.isEmpty then throwError "FRESH_EMPTY_INVENTORY"
  let allowed : List Name := [`propext,`Classical.choice,`Quot.sound]
  let mut seen : List Name := []
  let mut bad : Nat := 0
  for (n,i) in env.constants.toList do
    if let some idx := env.getModuleIdxFor? n then
      let origin := env.allImportedModuleNames[idx.toNat]!
      if modules.contains origin then
        seen := origin :: seen
        let axs ← collectAxioms n
        let reject := i.isAxiom || i.isUnsafe || (axs.toList.any (fun a => !allowed.contains a))
        if reject then bad := bad+1
        logInfo m!"DECL|{origin}|{n}|{i.isAxiom}|{i.isUnsafe}|{String.intercalate "," (axs.toList.map Name.toString)}|{reject}"
  for origin in modules do
    let count := (seen.filter (· == origin)).length
    logInfo m!"COUNT|{origin}|{count}"
    if count == 0 then throwError "FRESH_MISSING_ORIGIN"
  logInfo m!"BAD|{bad}"
  if bad > 0 then throwError "FRESH_CUSTOM_OR_UNSAFE"
