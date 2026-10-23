import Lean
open Lean
def main (args : List String) : IO Unit := do
  initSearchPath (← findSysroot)
  let names := args.map String.toName
  let env ← importModules (names.toArray.map fun n => {module := n}) {}
  let mut producerRows : Array Json := #[]
  let mut resolved : NameSet := {}
  let mut libraries : Array Json := #[]
  for h : i in [0:env.header.modules.size] do
    let mod := env.header.modules[i].module
    let md := env.header.moduleData[i]!
    if names.contains mod then
      for n in md.constNames do resolved := resolved.insert n
      let extras := md.extraConstNames.map (fun n => Json.mkObj [
        ("name",toJson n.toString),("has_constant_info",toJson (env.find? n |>.isSome))])
      producerRows := producerRows.push <| Json.mkObj [
        ("producer",toJson mod.toString),("stored_count",toJson md.constants.size),
        ("stored_names",toJson (md.constNames.map toString)),
        ("imports",toJson (md.imports.map (fun x => x.module.toString))),
        ("extra_names",toJson extras)]
    else
      let path ← findOLean mod
      libraries := libraries.push <| Json.mkObj [("module",toJson mod.toString),("olean",toJson path.toString)]
  let resolvedRows := resolved.toList.map (fun n => Json.mkObj [
    ("name",toJson n.toString),("producer",toJson (match env.getModuleIdxFor? n with
      | none => "MISSING"
      | some idx => env.header.modules[idx]!.module.toString))])
  IO.println <| (Json.mkObj [("scientific_producers",toJson producerRows),
    ("resolved_scientific",toJson resolvedRows),("installed_modules",toJson libraries)]).compress
