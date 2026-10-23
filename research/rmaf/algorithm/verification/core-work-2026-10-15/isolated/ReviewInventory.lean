import Lean
import Controls
open Lean Elab Command

def workReviewKind : ConstantInfo → String
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
  let wanted := ["RMAF","Geometry","Bridge","Composition","CoreGraph","CherryCoarsening","CoreProgram","CoreInvariants","SourceBridge","Contraction","Normalization","InitialLift","Suppression","EraseLift","Origins","Branches","Work","Primitive","Payload","Controls"]
  for (name, ci) in env.constants.toList do
    if let some idx := env.getModuleIdxFor? name then
      let origin := env.header.moduleNames[idx.toNat]!.toString
      if wanted.contains origin then
        let axs ← Lean.collectAxioms name
        let row := Json.mkObj [("name",toJson name.toString),("origin",toJson origin),
          ("kind",toJson (workReviewKind ci)),("axioms",toJson (axs.map Name.toString))]
        logInfo m!"WORK_REVIEW_ROW {row.compress}"
