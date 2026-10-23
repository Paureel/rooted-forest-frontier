import Lean
/- One-shot independent stored-producer instrument. Reads actual ModuleData
   ConstantInfo before resolved-name coalescing; no scientific source imports. -/
open Lean

def allRefs (ci : ConstantInfo) : NameSet :=
  let refs := ci.getUsedConstantsAsSet
  match ci with
  | .recInfo val => val.rules.foldl (fun out r => out ++ r.rhs.getUsedConstantsAsSet) refs
  | _ => refs

def recursorRules (ci : ConstantInfo) : Json :=
  match ci with
  | .recInfo val => toJson <| val.rules.map fun r => Json.mkObj [
      ("ctor",toJson r.ctor.toString),("nfields",toJson r.nfields),("rhs",toJson (reprStr r.rhs))]
  | _ => toJson ([] : List Json)

def actualBody (ci : ConstantInfo) : Json :=
  match ci.value? (allowOpaque := true) with
  | some v => toJson (reprStr v)
  | none => Json.null

def kindOf : ConstantInfo → String
  | .axiomInfo _ => "axiom"
  | .thmInfo _ => "theorem"
  | .defnInfo _ => "definition"
  | .opaqueInfo _ => "opaque"
  | .quotInfo _ => "quotient"
  | .inductInfo _ => "inductive"
  | .ctorInfo _ => "constructor"
  | .recInfo _ => "recursor"

partial def walkRefs (env : Environment) (todo : List Name)
    (seen : NameSet := {}) (axioms : Array String := #[])
    (missing : Array String := #[]) : Array String × Array String :=
  match todo with
  | [] => (axioms,missing)
  | n :: rest =>
    if seen.contains n then walkRefs env rest seen axioms missing else
      let seen := seen.insert n
      match env.find? n with
      | none => walkRefs env rest seen axioms (missing.push n.toString)
      | some ci =>
        let axioms := match ci with
          | .axiomInfo _ => axioms.push n.toString
          | _ => axioms
        walkRefs env ((allRefs ci).toList ++ rest) seen axioms missing

def occurrence (env : Environment) (producer : Name) (idx : Nat)
    (ci : ConstantInfo) : Json := Id.run do
  let (axs,missing) := walkRefs env (allRefs ci).toList
  let directAxiom := kindOf ci == "axiom"
  let axs := if directAxiom then axs.push ci.name.toString else axs
  let resolved := match env.getModuleIdxFor? ci.name with
    | some n => env.header.moduleNames[n.toNat]!.toString
    | none => "UNRESOLVED"
  let resolvedKind := match env.find? ci.name with
    | some r => kindOf r
    | none => "UNRESOLVED"
  return Json.mkObj [
    ("producer",toJson producer.toString), ("index",toJson idx),
    ("name",toJson ci.name.toString), ("kind",toJson (kindOf ci)),
    ("resolved_origin",toJson resolved), ("resolved_kind",toJson resolvedKind),
    ("type",toJson (reprStr ci.type)),
    ("body",match ci.value? (allowOpaque := true) with
      | some v => toJson (reprStr v)
      | none => Json.null),
    ("references",toJson ((allRefs ci).toList.map Name.toString)),
    ("recursor_rules",recursorRules ci),
    ("unsafe",toJson ci.isUnsafe),("partial",toJson ci.isPartial),
    ("resolved_type",match env.find? ci.name with | some r => toJson (reprStr r.type) | none => Json.null),
    ("resolved_body",match env.find? ci.name with | some r => actualBody r | none => Json.null),
    ("resolved_recursor_rules",match env.find? ci.name with | some r => recursorRules r | none => Json.null),
    ("axioms",toJson axs), ("missing",toJson missing)]

unsafe def main (args : List String) : IO UInt32 := do
  initSearchPath (← findSysroot)
  let importNames := args.takeWhile (· != "--producers")
  let producerNames := if args.contains "--producers" then (args.dropWhile (· != "--producers")).drop 1 else args
  let imports := importNames.toArray.map fun s => ({ module := s.toName } : Import)
  let env ← importModules imports {} (trustLevel := 0)
  let mut producers : Array Json := #[]
  let mut rows : Array Json := #[]
  for s in producerNames do
    let name := s.toName
    let some midx := env.getModuleIdx? name | throw (IO.userError s!"no producer {s}")
    let data := env.header.moduleData[midx.toNat]!
    if data.constants.size != data.constNames.size then throw (IO.userError "unequal stored arrays")
    for i in [:data.constants.size] do
      let ci := data.constants[i]!
      if ci.name != data.constNames[i]! then throw (IO.userError "stored name mismatch")
      rows := rows.push (occurrence env name i ci)
    producers := producers.push <| Json.mkObj [
      ("module",toJson s), ("count",toJson data.constants.size),
      ("imports",toJson (data.imports.map fun i => i.module.toString)),
      ("stored_extra_const_names",toJson (data.extraConstNames.map Name.toString))]
  IO.println <| (Json.mkObj [("producers",toJson producers),("rows",toJson rows),
    ("trustLevel",toJson env.header.trustLevel.toNat),
    ("loaded_modules",toJson (env.header.moduleNames.map Name.toString)),
    ("scope",toJson "stored producer ConstantInfo including recursor RHS before coalescing; compiler-only IR auxiliary bodies and installed trusted standard-library validation excluded")]).compress
  return 0
