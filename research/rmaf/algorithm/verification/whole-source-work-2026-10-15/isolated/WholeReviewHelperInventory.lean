import Lean
import WholeReviewSupplementClean
open Lean Elab Command

def wholeReviewKind : ConstantInfo → String
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
 let wanted := ["Branches", "Bridge", "CherryCoarsening", "ColorBudget", "ColorSteps", "ColorWork", "Composition", "Contraction", "CoreGraph", "CoreInvariants", "CoreProgram", "Coverage", "CutRecords", "Entrypoint", "EraseLift", "FullTransport", "Geometry", "GeometryWork", "InitialLift", "MassControls", "Normalization", "OriginalColors", "Origins", "OutputBudget", "OwnershipWork", "Payload", "Primitive", "RMAF", "RationalMass", "RawMass", "RuntimeAssembly", "SourceBridge", "Suppression", "WholeColors", "WholeMass", "Work", "WorkControls", "WholeReviewSourceBounds", "WholeReviewSupplementClean"]
 for (n,ci) in env.constants.toList do
  if let some idx := env.getModuleIdxFor? n then
   let origin := env.header.moduleNames[idx.toNat]!.toString
   if wanted.contains origin then
    let axs ← Lean.collectAxioms n
    let row := Json.mkObj [("name",toJson n.toString),("origin",toJson origin),("kind",toJson (wholeReviewKind ci)),("axioms",toJson (axs.map Name.toString))]
    logInfo m!"WHOLE_ORIGIN_ROW {row.compress}"
