import Lean

/- One-shot blind producer-array audit. No scientific candidate imports here.
   The command-line producer names are imported only when this file is run. -/
open Lean

def kindOf : ConstantInfo → String
  | .axiomInfo _ => "axiom"
  | .defnInfo _ => "definition"
  | .thmInfo _ => "theorem"
  | .opaqueInfo _ => "opaque"
  | .quotInfo _ => "quotient"
  | .inductInfo _ => "inductive"
  | .ctorInfo _ => "constructor"
  | .recInfo _ => "recursor"

def directNames (ci : ConstantInfo) : Array Name := Id.run do
  let mut ns := ci.type.getUsedConstants
  if let some v := ci.value? (allowOpaque := true) then
    for n in v.getUsedConstants do
      if !ns.contains n then ns := ns.push n
  return ns

partial def walkAxioms (env : Environment) (todo : List Name) (seen : List Name)
    (axioms missing : List Name) : List Name × List Name :=
  match todo with
  | [] => (axioms, missing)
  | n :: rest =>
    if seen.contains n then walkAxioms env rest seen axioms missing
    else match env.find? n with
    | none => walkAxioms env rest (n::seen) axioms (n::missing)
    | some ci =>
      let ax := match ci with | .axiomInfo _ => n::axioms | _ => axioms
      walkAxioms env (directNames ci |>.toList ++ rest) (n::seen) ax missing

def strings (xs : Array Name) : Json := toJson (xs.map toString)

def main (args : List String) : IO UInt32 := do
  initSearchPath (← findSysroot)
  if args.isEmpty then throw <| IO.userError "producer list must be nonempty"
  let requested := args.map String.toName
  let env ← importModules (requested.toArray.map fun n => {module := n}) {}
  let mut rows : Array Json := #[]
  let mut visited : Array String := #[]
  let mut forbidden : Array String := #[]
  let mut unresolved : Array String := #[]
  let mut inventories : Array Json := #[]
  let standardAxioms := [``propext, ``Classical.choice, ``Quot.sound]
  for h : i in [0:env.header.modules.size] do
    let producer := env.header.modules[i].module
    if requested.contains producer then
      visited := visited.push producer.toString
      let md := env.header.moduleData[i]!
      inventories := inventories.push <| Json.mkObj [
        ("producer",toJson producer.toString),("count",toJson md.constants.size),
        ("names",strings md.constNames),
        ("imports",toJson (md.imports.map (fun x => x.module.toString)))]
      if md.constants.size != md.constNames.size then
        throw <| IO.userError s!"stored name/occurrence mismatch {producer}"
      for j in [:md.constants.size] do
        let ci := md.constants[j]!
        if md.constNames[j]! != ci.name then
          throw <| IO.userError s!"stored name mismatch {producer}:{j}"
        let (axs, missing) := walkAxioms env (directNames ci).toList [] [] []
        let allAxs := match ci with | .axiomInfo _ => ci.name::axs | _ => axs
        for ax in allAxs do
          if !standardAxioms.contains ax then
            forbidden := forbidden.push s!"{producer}:{j}:{ci.name}:{ax}"
        for n in missing do unresolved := unresolved.push s!"{producer}:{j}:{n}"
        let resolved := match env.getModuleIdxFor? ci.name with
          | none => "NO_RESOLVED_PRODUCER"
          | some idx => env.header.modules[idx]!.module.toString
        rows := rows.push <| Json.mkObj [
          ("producer", toJson producer.toString), ("index", toJson j),
          ("name", toJson ci.name.toString), ("kind", toJson (kindOf ci)),
          ("resolved_producer", toJson resolved),
          ("type", toJson (reprStr ci.type)),
          ("body", toJson (ci.value? true |>.map reprStr)),
          ("references", strings (directNames ci)),
          ("axioms", toJson (allAxs.map toString)),
          ("imports", toJson (md.imports.map (fun x => x.module.toString)))]
  if visited.size != requested.length then
    throw <| IO.userError s!"missing producer: requested{requested.length} visited{visited.size}"
  let ok := forbidden.isEmpty && unresolved.isEmpty
  IO.println <| (Json.mkObj [("ok",toJson ok), ("producers",toJson visited),
    ("occurrence_count",toJson rows.size), ("forbidden",toJson forbidden),
    ("unresolved",toJson unresolved), ("inventories",toJson inventories),
    ("occurrences",toJson rows)]).compress
  return if ok then 0 else 2
