import SolResolvedV3
open Lean Elab Command
elab "#sol_generated_bodies" : command => do
  let e ← getEnv
  let names : List Name := [] -- Literal adapter replaced from retained110 new-name record.
  for n in names do
    let some ci := e.find? n | throwError "missing exact generated occurrence {n}"
    let axs ← liftCoreM <| collectAxioms n
    let raw := match e.getModuleIdxFor? n with
      | some i => toString e.header.moduleNames[i.toNat]!
      | none => toString e.mainModule
    liftIO <| IO.println <| "GENERATED\t" ++ (Json.mkObj [
      ("name",toJson (toString n)),("rawOrigin",toJson raw),
      ("kind",toJson (match ci with | .thmInfo _ => "theorem" | .axiomInfo _ => "axiom" | .defnInfo _ => "definition" | _ => "other")),
      ("levelParams",toJson (ci.levelParams.map toString)),
      ("typeExpr",toJson (reprStr ci.type)),
      ("valueExpr",match ci.value? true with | some v => toJson (reprStr v) | none => Json.null),
      ("axioms",toJson (axs.toList.map toString))]).compress
