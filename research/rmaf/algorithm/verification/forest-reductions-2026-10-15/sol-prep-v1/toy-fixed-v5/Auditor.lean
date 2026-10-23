import Lean
open Lean Elab Command
/-- One-shot reviewer auditor: no imported author/reviewer audit code. -/
elab "#sol_inventory " tag:str : command => do
  let env ← getEnv
  let rows := env.constants.toList
  for (n, ci) in rows do
    let origin := match env.getModuleIdxFor? n with
      | some i => toString env.header.moduleNames[i.toNat]!
      | none => toString env.mainModule
    if origin.startsWith "Toy" then
      let kind := match ci with
        | .axiomInfo _ => "axiom"
        | .thmInfo _ => "theorem"
        | .defnInfo _ => "definition"
        | .opaqueInfo _ => "opaque"
        | .quotInfo _ => "quot"
        | .inductInfo _ => "inductive"
        | .ctorInfo _ => "constructor"
        | .recInfo _ => "recursor"
      let axioms ← liftCoreM <| collectAxioms n
      liftIO <| IO.println <| "ROW\t" ++ tag.getString ++ "\t" ++ toString n ++ "\t" ++ origin ++ "\t" ++ kind ++ "\t" ++ String.intercalate "," (axioms.toList.map toString)
