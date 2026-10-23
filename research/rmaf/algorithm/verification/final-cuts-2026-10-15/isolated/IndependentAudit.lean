import Lean
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
import AssemblyControls
import RankCost
import MinimumUnique
import TailMass
import ColorClasses
import RecoveryProgram
import BlockColors
import Controls
import Work
import Payload
import Primitive
import CoreWorkControls
import CutControls
import FinalRecoveryControls
import Permutations
import Recovery
import FinalWork
import FinalRegression
import RankControls
import Regression
open Lean Elab Command

def toyKind : ConstantInfo → String
 | .axiomInfo _ => "axiom"
 | .defnInfo _ => "definition"
 | .thmInfo _ => "theorem"
 | .opaqueInfo _ => "opaque"
 | .quotInfo _ => "quotient"
 | .inductInfo _ => "inductive"
 | .ctorInfo _ => "constructor"
 | .recInfo _ => "recursor"
run_cmd do
 let env ← getEnv
 for (n,c) in env.constants.toList do
  if let some i := env.getModuleIdxFor? n then
   let origin := env.header.moduleNames[i.toNat]!.toString
   if ["RMAF", "CoreGraph", "Geometry", "Bridge", "Composition", "SourceBridge", "CherryCoarsening", "CoreProgram", "CoreInvariants", "Contraction", "Normalization", "InitialLift", "Suppression", "EraseLift", "Origins", "Branches", "CutRecords", "FullTransport", "Coverage", "Entrypoint", "OutputBudget", "ColorBudget", "ColorSteps", "RawMass", "RationalMass", "ParentColors", "OriginalGraph", "Display", "Regions", "History", "Realization", "OwnerCover", "CutCoverage", "InitialCoverage", "Cost", "ValidPartition", "WholeSource", "Requests", "OwnershipBase", "ChainAssembly", "SourceValidity", "ForestOutputs", "AssemblyControls", "RankCost", "MinimumUnique", "TailMass", "ColorClasses", "RecoveryProgram", "BlockColors", "Controls", "Work", "Payload", "Primitive", "CoreWorkControls", "CutControls", "FinalRecoveryControls", "Permutations", "Recovery", "FinalWork", "FinalRegression", "RankControls", "Regression"].contains origin then
    let axs ← Lean.collectAxioms n
    let body := c.value? (allowOpaque := true)
    let typeNames := c.type.getUsedConstants.toList.map Name.toString
    let bodyNames := match body with | none => [] | some v => v.getUsedConstants.toList.map Name.toString
    let bodyHash : Json := match body with | none => Json.null | some v => toJson (hash v).toNat
    let row := Json.mkObj [("name",toJson n.toString),("origin",toJson origin),("kind",toJson (toyKind c)),("type_structural_hash",toJson (hash c.type).toNat),("body_structural_hash",bodyHash),("type_constants",toJson typeNames),("body_constants",toJson bodyNames),("axioms",toJson (axs.map Name.toString))]
    logInfo m!"REVIEW_ORIGIN {row.compress}"
