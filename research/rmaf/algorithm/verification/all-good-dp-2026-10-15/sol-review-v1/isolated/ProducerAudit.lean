import Lean
open Lean Elab Command

private def kind (c : ConstantInfo) : String :=
  match c with
  | .axiomInfo _ => "axiom"
  | .defnInfo _ => "definition"
  | .thmInfo _ => "theorem"
  | .opaqueInfo _ => "opaque"
  | .quotInfo _ => "quot"
  | .inductInfo _ => "inductive"
  | .ctorInfo _ => "constructor"
  | .recInfo _ => "recursor"

private def js (s : String) : Json := toJson s
private def origin (e : Environment) (n : Name) : String :=
  match e.getModuleIdxFor? n with
  | some i => toString e.header.moduleNames[i.toNat]!
  | none => toString e.mainModule

private def rawInfo (ci : ConstantInfo) : Json := Json.mkObj [
  ("name", js (toString ci.name)), ("kind", js (kind ci)),
  ("levelParams", toJson (ci.levelParams.map toString)),
  ("typeExpr", js (reprStr ci.type)),
  ("valueExpr", match ci.value? true with | some v => js (reprStr v) | none => Json.null)]

/-- Stored producer arrays, retaining occurrences before resolved-name coalescing. -/
elab "#sol_producers " names:str : command => do
  let e ← getEnv
  let wanted := names.getString.splitOn ","
  liftIO <| IO.println <| "MODULES\t" ++ (toJson (e.header.moduleNames.toList.map toString)).compress
  for i in [:e.header.moduleNames.size] do
    let moduleName := toString e.header.moduleNames[i]!
    if wanted.contains moduleName then
      let data := e.header.moduleData[i]!
      let oleanPath ← liftIO <| findOLean e.header.moduleNames[i]!
      liftIO <| IO.println <| "PRODUCER\t" ++ (Json.mkObj [
        ("producer", js moduleName), ("moduleIndex", toJson i),
        ("oleanPath", js oleanPath.toString),
        ("constNames", toJson (data.constNames.toList.map toString)),
        ("imports", toJson (data.imports.toList.map (fun x => toString x.module))),
        ("extraConstNames", toJson (data.extraConstNames.toList.map toString))]).compress
      for j in [:data.constants.size] do
        let ci := data.constants[j]!
        let mut refs := ci.type.getUsedConstants
        if let some v := ci.value? true then
          refs := refs ++ v.getUsedConstants
        if let .inductInfo v := ci then
          refs := refs ++ v.ctors.toArray
        let mut refRows := #[]
        for n in refs do
          let axs ← liftCoreM <| collectAxioms n
          refRows := refRows.push <| Json.mkObj [
            ("name", js (toString n)), ("resolvedOrigin", js (origin e n)),
            ("resolvedKind", match e.find? n with | some c => js (kind c) | none => js "MISSING"),
            ("resolvedAxioms", toJson (axs.toList.map toString))]
        let resolved := match e.find? ci.name with | some c => rawInfo c | none => Json.null
        let row := Json.mkObj [
          ("producer", js moduleName), ("moduleIndex", toJson i), ("occurrenceIndex", toJson j),
          ("stored", rawInfo ci), ("resolvedOrigin", js (origin e ci.name)),
          ("resolved", resolved), ("references", Json.arr refRows)]
        liftIO <| IO.println <| "OCCURRENCE\t" ++ row.compress
