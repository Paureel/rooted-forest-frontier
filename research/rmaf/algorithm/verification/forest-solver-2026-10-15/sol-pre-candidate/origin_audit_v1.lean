import Lean

/- One-shot fresh all-module-origin review instrument. The scientific toy and
   future scientific modules are imported dynamically; the auditor imports Lean
   as tooling only. No project audit source was read or reused. -/
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

def allExprs (ci : ConstantInfo) : Array Expr := Id.run do
  let mut xs := #[ci.type]
  if let some e := ci.value? true then xs := xs.push e
  if let .recInfo v := ci then
    for r in v.rules do xs := xs.push r.rhs
  return xs

def recursorDetails (ci : ConstantInfo) : Json :=
  match ci with
  | .recInfo v => Json.mkObj [
      ("parameters",toJson v.numParams),("indices",toJson v.numIndices),
      ("motives",toJson v.numMotives),("minors",toJson v.numMinors),
      ("all",toJson (v.all.map toString)),("k",toJson v.k),
      ("rules",Json.arr (v.rules.toArray.map fun r => Json.mkObj [
        ("constructor",toJson (toString r.ctor)),("fields",toJson r.nfields),
        ("body",toJson (reprStr r.rhs))]))]
  | _ => Json.null

def extraDetails (ci : ConstantInfo) : Json :=
  match ci with
  | .inductInfo v => Json.mkObj [
      ("constructors",toJson (v.ctors.map toString)),
      ("parameters",toJson v.numParams),("indices",toJson v.numIndices),
      ("all",toJson (v.all.map toString)),("recursive",toJson v.isRec),
      ("nested",toJson v.isNested), ("reflexive",toJson v.isReflexive)]
  | .ctorInfo v => Json.mkObj [
      ("inductive",toJson (toString v.induct)),("index",toJson v.cidx),
      ("parameters",toJson v.numParams),("fields",toJson v.numFields)]
  | .recInfo _ => recursorDetails ci
  | _ => Json.null

def record (origin : String) (n : Name) (ci : ConstantInfo) : CoreM Json := do
  let axs ← collectAxioms n
  let deps := ((allExprs ci).foldl (fun ns e =>
    e.getUsedConstants.foldl (fun ns n => if ns.contains n then ns else ns.push n) ns) #[]).qsort Name.lt
  return Json.mkObj [
    ("name",toJson (toString n)),("origin",toJson origin),
    ("kind",toJson (kindOf ci)),("universe_parameters",toJson (ci.levelParams.map toString)),
    ("type",toJson (reprStr ci.type)),
    ("body",match ci.value? true with | none => Json.null | some e => toJson (reprStr e)),
    ("extra",extraDetails ci), ("unsafe",toJson ci.isUnsafe),
    ("partial",toJson ci.isPartial),
    ("dependencies",toJson (deps.toList.map toString)),
    ("axioms",toJson (axs.toList.map toString))]

def audit (env : Environment) (origins : List String) : CoreM Json := do
  let all := env.constants.fold (fun xs n ci => xs.push (n,ci)) #[]
  let mut records := #[]
  let mut moduleCounts : Std.HashMap String Nat := {}
  for (n,ci) in all do
    if let some idx := env.getModuleIdxFor? n then
      let origin := toString env.header.moduleNames[idx.toNat]!
      moduleCounts := moduleCounts.insert origin (moduleCounts[origin]?.getD 0 + 1)
      if origins.contains origin then
        records := records.push (← record origin n ci)
  let counts := moduleCounts.toArray.qsort (fun a b => a.1 < b.1)
  return Json.mkObj [
    ("schema",toJson "fresh-full-origin-v1"),
    ("requested_origins",toJson origins),
    ("environment_modules",toJson (env.header.moduleNames.toList.map toString)),
    ("all_module_origin_counts",Json.arr (counts.map fun (n,c) =>
        Json.mkObj [("origin",toJson n),("count",toJson c)])),
    ("origin_count",toJson records.size),("records",Json.arr records)]

def main (args : List String) : IO UInt32 := do
  if args.length < 3 then
    IO.eprintln "usage: --run origin_audit.lean IMPORT_ROOT OUTPUT ORIGIN..."
    return 2
  initSearchPath (← findSysroot)
  let env ← importModules #[{module := args[0]!.toName}] {}
  let json ← CoreM.toIO' (audit env (args.drop 2))
      {fileName := "<fresh-origin-audit>",fileMap := default, maxRecDepth := 1000000}
      {env := env.setExporting false}
  IO.FS.writeFile args[1]! (json.pretty ++ "\n")
  IO.println s!"inventory written: {args[1]!}"
  return 0
