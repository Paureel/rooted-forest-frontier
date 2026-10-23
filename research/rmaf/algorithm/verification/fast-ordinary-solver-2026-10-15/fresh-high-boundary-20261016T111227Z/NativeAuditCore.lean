-- Target-local audit instrument. Official compacted-region serialization,
-- exact same erased payload type at save/read, no closures, live depRegions.
-- Instrument unsafe IO is not a premise or dependency of any mathematical proof.
import Boundary26
import Lean
set_option linter.unusedVariables false
open Lean Elab Command
namespace StageAudit
structure BodyRecord where
  name : Name
  moduleName : Name
  levels : List Name
  kind : String
  type : Expr
  body : Option Expr
  rules : Array (Name × Nat × Expr)
  isUnsafe : Bool
  isPartial : Bool
def kind (c : ConstantInfo) : String :=
  match c with
  | .axiomInfo _ => "axiom" | .defnInfo _ => "definition" | .thmInfo _ => "theorem"
  | .opaqueInfo _ => "opaque" | .quotInfo _ => "quotient-primitive"
  | .inductInfo _ => "inductive" | .ctorInfo _ => "constructor" | .recInfo _ => "recursor"
def forbidden : Array String := #["Universal233.CherryBranching.actual_pendant_safety",
 "Universal233.CherryBranching.actual_high_safety", "actual_t1_pendant_exchange", "T1Exchange",
 "ordinary_branches_cover", "found_globally_minimum", "OrdinaryDispatch.FastOrdinary.solve_exact",
 "exactOneRule", "exactHighRule", "high_rule_if_dichotomy", "one_rule_if_exchange",
 "IndependentPaid.CherryForestDichotomy", "sorryAx"]
def blocked (n : Name) : Bool := forbidden.any fun s => decide ((n.toString.splitOn s).length > 1)
def exactOption (a b : Option Expr) : Bool := match a,b with
  | none,none => true | some a,some b => Expr.equal a b | _,_ => false
def exactRecord (a b : BodyRecord) : Bool :=
  a.name == b.name && a.moduleName == b.moduleName && a.levels == b.levels && a.kind == b.kind &&
  a.isUnsafe == b.isUnsafe && a.isPartial == b.isPartial && Expr.equal a.type b.type && exactOption a.body b.body &&
  a.rules.size == b.rules.size && (a.rules.zip b.rules).all (fun (x,y) =>
    x.1 == y.1 && x.2.1 == y.2.1 && Expr.equal x.2.2 y.2.2)
unsafe def audit (roots : Array Name) (stem : String) : CommandElabM Unit := do
  let env ← getEnv
  let mut todo := roots
  let mut seen : NameHashSet := {}
  let mut rows : Array Json := #[]
  let mut records : Array BodyRecord := #[]
  let mut axioms : Array String := #[]
  while !todo.isEmpty do
    let n := todo.back!
    todo := todo.pop
    if seen.contains n then continue
    seen := seen.insert n
    if blocked n then throwError "FORBIDDEN_REACHED {n}"
    let some ci := env.find? n | throwError "UNKNOWN_DECLARATION {n}"
    if ci.isUnsafe || ci.isPartial then throwError "UNSAFE_OR_PARTIAL {n}"
    let mod := match env.getModuleIdxFor? n with
      | some i => env.header.moduleNames[i.toNat]!
      | none => env.header.mainModule
    let body := ci.value? (allowOpaque := true)
    if ["definition","theorem","opaque"].contains (kind ci) && body.isNone then
      throwError "MISSING_STORED_BODY {n}"
    let mut refs := ci.getUsedConstantsAsSet.toArray
    let mut rules : Array (Name × Nat × Expr) := #[]
    if let .recInfo rv := ci then
      for rule in rv.rules do
        refs := refs ++ rule.rhs.getUsedConstants
        rules := rules.push (rule.ctor,rule.nfields,rule.rhs)
    todo := todo ++ refs
    if kind ci == "axiom" then
      unless ["Quot.sound","propext","Classical.choice"].contains n.toString do throwError "NONSTANDARD_AXIOM {n}"
      axioms := axioms.push n.toString
    rows := rows.push (Json.mkObj [("record",toJson "dependency"),("name",toJson n.toString),
      ("module",toJson mod.toString),("kind",toJson (kind ci)),("body_present",toJson body.isSome),
      ("isUnsafe",toJson ci.isUnsafe),("isPartial",toJson ci.isPartial),("refs",toJson (refs.map Name.toString))])
    unless ["Init","Std","Lean"].any (fun p => p.isPrefixOf mod.toString) do
      records := records.push ⟨n,mod,ci.levelParams,kind ci,ci.type,body,rules,ci.isUnsafe,ci.isPartial⟩
  IO.FS.createDirAll "exports"
  let path := System.FilePath.mk ("exports/" ++ stem ++ ".body.olean")
  let _ ← CompactedRegion.save path (Name.str `StageAudit stem) records env.header.regions none
  let (restored, _region) ← CompactedRegion.read (α := Array BodyRecord) path env.header.regions
  unless records.size == restored.size && (records.zip restored).all (fun (a,b) => exactRecord a b) do
    throwError "EXACT_NATIVE_ROUNDTRIP_FAILED"
  let bytes ← IO.FS.readBinFile path
  unless bytes.size <= 4*1024*1024 do throwError "COMPACT_BODY_CHUNK_OVER_4MIB"
  IO.println ((Json.mkObj [("record",toJson "header"),("version",toJson (1 : Nat)),
    ("roots",toJson (roots.map Name.toString))]).compress)
  for row in rows do IO.println row.compress
  for region in env.header.regions do
    IO.println ((Json.mkObj [("record",toJson "region"),("path",toJson region.filePath.toString),
      ("bytes",toJson region.size.toNat)]).compress)
  IO.println ((Json.mkObj [("record",toJson "summary"),("declarations",toJson rows.size),
    ("native_body_records",toJson records.size),("axioms",toJson axioms),
    ("body_path",toJson path.toString),("body_bytes",toJson bytes.size),
    ("exact_roundtrip",toJson true),("forbidden",toJson (#[] : Array String)),
    ("unknown",toJson (#[] : Array String))]).compress)
end StageAudit
