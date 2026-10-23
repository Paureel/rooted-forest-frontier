import Lean
import RMAF
import CoreGraph
import CherryCoarsening
import Geometry
import Bridge
import Composition
import SourceBridge
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
import OriginalGraph
import Display
import Regions
import History
import Realization
import OwnerCover
import FullTransport
import Coverage
import Entrypoint
import OutputBudget
import ColorBudget
import ColorSteps
import RawMass
import RationalMass
import ParentColors
import CutCoverage
import InitialCoverage
import Cost
import ValidPartition
import WholeSource
import Requests
import OwnershipBase
import ChainAssembly
import SourceValidity
import RankCost
import MinimumUnique
import TailMass
import ColorClasses
import Probe
import Work
import ProbeWork
import FourProbe
import OptimizedWork
import ProbePrecontrols
import ProbeControls
import CutControls
import ForestOutputs
import AssemblyControls
import Controls
import Regression
import RankControls
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
   if ["RMAF", "CoreGraph", "CherryCoarsening", "Geometry", "Bridge", "Composition", "SourceBridge", "CoreProgram", "CoreInvariants", "Contraction", "Normalization", "InitialLift", "Suppression", "EraseLift", "Origins", "Branches", "CutRecords", "OriginalGraph", "Display", "Regions", "History", "Realization", "OwnerCover", "FullTransport", "Coverage", "Entrypoint", "OutputBudget", "ColorBudget", "ColorSteps", "RawMass", "RationalMass", "ParentColors", "CutCoverage", "InitialCoverage", "Cost", "ValidPartition", "WholeSource", "Requests", "OwnershipBase", "ChainAssembly", "SourceValidity", "RankCost", "MinimumUnique", "TailMass", "ColorClasses", "Probe", "Work", "ProbeWork", "FourProbe", "OptimizedWork", "ProbePrecontrols", "ProbeControls", "CutControls", "ForestOutputs", "AssemblyControls", "Controls", "Regression", "RankControls"].contains origin then
    let axs ← Lean.collectAxioms n
    let row := Json.mkObj [("name",toJson n.toString),("origin",toJson origin),("kind",toJson (toyKind c)),("axioms",toJson (axs.map Name.toString))]
    logInfo m!"REVIEW_ORIGIN {row.compress}"
