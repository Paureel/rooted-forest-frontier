import Lean
import ReviewPlantUsed
import ReviewPlantUnused
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
   if ["ReviewPlantUsed","ReviewPlantUnused"].contains origin then
    let axs ← Lean.collectAxioms n
    let row := Json.mkObj [("name",toJson n.toString),("origin",toJson origin),("kind",toJson (toyKind c)),("axioms",toJson (axs.map Name.toString))]
    logInfo m!"PLANT_ORIGIN {row.compress}"
