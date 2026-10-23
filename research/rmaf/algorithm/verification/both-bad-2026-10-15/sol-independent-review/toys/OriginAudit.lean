import Lean

/- One-shot fresh full-origin toy scanner using compiler APIs only. -/
open Lean Elab Command

private def constantKind : ConstantInfo → String
  | .axiomInfo _ => "axiom"
  | .defnInfo _ => "def"
  | .thmInfo _ => "theorem"
  | .opaqueInfo _ => "opaque"
  | .quotInfo _ => "quotient"
  | .inductInfo _ => "inductive"
  | .ctorInfo _ => "constructor"
  | .recInfo _ => "recursor"

private def strings (xs : Array String) : Json :=
  .arr (xs.map Json.str)

elab "audit_origins! " destination:str : command => do
  let env ← getEnv
  let mut records : Array Json := #[]
  let mut rejected : Array String := #[]
  let standard : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]
  for (n, c) in env.constants.toList do
    if let some idx := env.getModuleIdxFor? n then
      let origin := env.header.moduleNames[idx.toNat]!
      if origin.toString.startsWith "Toy" then
        let axs ← collectAxioms n
        for ax in axs do
          if !standard.contains ax then rejected := rejected.push s!"{n}:{ax}"
        if constantKind c == "axiom" && !standard.contains n then
          rejected := rejected.push s!"unused-or-used-origin-axiom:{n}"
        let body := match c.value? (allowOpaque := true) with
          | some e => Json.str (reprStr e)
          | none => Json.null
        records := records.push <| Json.mkObj [
          ("name", .str n.toString),
          ("origin", .str origin.toString),
          ("module_index", toJson idx.toNat),
          ("kind", .str (constantKind c)),
          ("type", .str (reprStr c.type)),
          ("body", body),
          ("dependencies", strings (c.getUsedConstantsAsSet.toArray.map Name.toString)),
          ("axioms", strings (axs.map Name.toString))]
  let imports := env.header.imports.map fun i => i.module.toString
  let allModules := env.header.moduleNames.map Name.toString
  let out := Json.mkObj [("records", .arr records), ("imports", strings imports),
    ("all_modules", strings allModules), ("rejected", strings rejected)]
  liftIO <| IO.FS.writeFile destination.getString out.pretty
  logInfo m!"FULL_ORIGIN_TOY records={records.size} rejected={rejected.size}"
