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
import FullTransport
import Coverage
import Entrypoint
import OutputBudget
import ColorBudget
import ColorSteps
import RawMass
import RationalMass
import Controls
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
import CutControls
import ParentColors
import WholeSource
import Requests
import OwnershipBase
import ChainAssembly
import SourceValidity
import ForestOutputs
import AssemblyControls
import RankCost
import MinimumUnique
import TailMass
import ColorClasses
import Regression
import RankControls
import ResRestriction
import ResEmbedding
import ResPartition
import ResCost
import ResForward
import ResReconstruction
import ResControls
import ResConsumers
import ConsumerInterfaceV2
import Lean
open Lean Elab Command
run_cmd do
  let env ← getEnv
  let requested : List Name := [`RMAF,`Geometry,`Bridge,`Composition,`CoreGraph,`CherryCoarsening,`CoreProgram,`CoreInvariants,`SourceBridge,`Contraction,`Normalization,`InitialLift,`Suppression,`EraseLift,`Origins,`Branches,`CutRecords,`FullTransport,`Coverage,`Entrypoint,`OutputBudget,`ColorBudget,`ColorSteps,`RawMass,`RationalMass,`Controls,`OriginalGraph,`Display,`Regions,`History,`Realization,`OwnerCover,`CutCoverage,`InitialCoverage,`Cost,`ValidPartition,`CutControls,`ParentColors,`WholeSource,`Requests,`OwnershipBase,`ChainAssembly,`SourceValidity,`ForestOutputs,`AssemblyControls,`RankCost,`MinimumUnique,`TailMass,`ColorClasses,`Regression,`RankControls,`ResRestriction,`ResEmbedding,`ResPartition,`ResCost,`ResForward,`ResReconstruction,`ResControls,`ResConsumers,`ConsumerInterfaceV2]
  if requested.isEmpty then throwError "FRESH_EMPTY_INVENTORY"
  let allowed : List Name := [`propext,`Classical.choice,`Quot.sound]
  let mut seen : List Name := []
  let mut bad : Nat := 0
  for (name,info) in env.constants.toList do
    if let some index := env.getModuleIdxFor? name then
      let origin := env.allImportedModuleNames[index.toNat]!
      if requested.contains origin then
        seen := origin :: seen
        let axioms ← collectAxioms name
        let nonstandard := axioms.toList.filter (fun x => !allowed.contains x)
        let rejected := info.isAxiom || info.isUnsafe || !nonstandard.isEmpty
        if rejected then bad := bad + 1
        logInfo m!"FRESH|{origin}|{name}|{info.isAxiom}|{info.isUnsafe}|{String.intercalate "," (axioms.toList.map Name.toString)}|{rejected}"
  for origin in requested do
    let n := (seen.filter (· == origin)).length
    logInfo m!"FRESH_COUNT|{origin}|{n}"
    if n == 0 then throwError m!"FRESH_MISSING_ORIGIN {origin}"
  logInfo m!"FRESH_BAD|{bad}"
  if bad > 0 then throwError "FRESH_AUDIT_REJECT"
