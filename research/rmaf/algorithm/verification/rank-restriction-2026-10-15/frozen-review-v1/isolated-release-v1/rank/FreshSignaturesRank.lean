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
import Lean
open Lean Elab Command
run_cmd do
  let env ← getEnv
  let modules : List Name := [`RMAF,`Geometry,`Bridge,`Composition,`CoreGraph,`CherryCoarsening,`CoreProgram,`CoreInvariants,`SourceBridge,`Contraction,`Normalization,`InitialLift,`Suppression,`EraseLift,`Origins,`Branches,`CutRecords,`FullTransport,`Coverage,`Entrypoint,`OutputBudget,`ColorBudget,`ColorSteps,`RawMass,`RationalMass,`Controls,`OriginalGraph,`Display,`Regions,`History,`Realization,`OwnerCover,`CutCoverage,`InitialCoverage,`Cost,`ValidPartition,`CutControls,`ParentColors,`WholeSource,`Requests,`OwnershipBase,`ChainAssembly,`SourceValidity,`ForestOutputs,`AssemblyControls,`RankCost,`MinimumUnique,`TailMass,`ColorClasses,`Regression,`RankControls]
  for m in modules do
    let p ← liftIO <| findOLean m
    logInfo m!"PATH|{m}|{p}"
  for (n,i) in env.constants.toList do
    if let some idx := env.getModuleIdxFor? n then
      let origin := env.allImportedModuleNames[idx.toNat]!
      if modules.contains origin then
        let value := i.value? true
        let j := Json.mkObj [("origin",toJson origin.toString),("name",toJson n.toString),
          ("type",toJson (reprStr i.type)),("type_hash",toJson i.type.hash.toNat),
          ("body",toJson (value.map reprStr)),("body_hash",toJson (value.map (fun e => e.hash.toNat)))]
        logInfo m!"SIGNATURE|{j.compress}"
