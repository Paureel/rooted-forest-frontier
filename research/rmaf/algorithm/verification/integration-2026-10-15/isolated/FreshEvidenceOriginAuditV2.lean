import FreshComparisons
import ScopeWitnessesV2
import Lean
open Lean Elab Command

run_cmd do
  let env ← getEnv
  let wanted : List String := ["FreshComparisons", "ScopeWitnessesV2"]
  let mut rows : Array Json := #[]
  for (name, info) in env.constants.toList do
    if let some idx := env.getModuleIdxFor? name then
      let origin := env.header.moduleNames[idx.toNat]!.toString
      if wanted.contains origin then
        let axs ← Lean.collectAxioms name
        let kind := match info with
          | .axiomInfo _ => "axiom"
          | .defnInfo _ => "definition"
          | .thmInfo _ => "theorem"
          | .opaqueInfo _ => "opaque"
          | .quotInfo _ => "quotient"
          | .inductInfo _ => "inductive"
          | .ctorInfo _ => "constructor"
          | .recInfo _ => "recursor"
        rows := rows.push <| Json.mkObj [
          ("name", toJson name.toString), ("origin", toJson origin),
          ("kind", toJson kind), ("axioms", toJson (axs.toList.map Name.toString))]
  logInfo m!"ORIGIN-AUDIT: {(Json.arr rows).compress}"
