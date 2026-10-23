import Lean

/- One-shot fresh all-module-origin review instrument. The scientific toy and
   future scientific modules are imported dynamically; the auditor imports Lean
   as tooling only. No project audit source was read or reused. -/
open Lean

structure ExprDAG where
  memo : ExprStructMap Nat := {}
  nodes : Array Json := #[]

partial def internExpr (e : Expr) : StateM ExprDAG Nat := do
  if let some i := (← get).memo[ExprStructEq.mk e]? then return i
  let row : Json ← match e with
    | .bvar i => pure <| Json.arr #[toJson "bvar",toJson i]
    | .fvar n => pure <| Json.arr #[toJson "fvar",toJson (reprStr n)]
    | .mvar n => pure <| Json.arr #[toJson "mvar",toJson (reprStr n)]
    | .sort u => pure <| Json.arr #[toJson "sort",toJson (reprStr u)]
    | .const n us => pure <| Json.arr #[toJson "const",toJson (reprStr n),toJson (us.map reprStr)]
    | .app f a => do return Json.arr #[toJson "app",toJson (← internExpr f),toJson (← internExpr a)]
    | .lam n t b bi => do return Json.arr #[toJson "lam",toJson (reprStr n),toJson (← internExpr t),toJson (← internExpr b),toJson (reprStr bi)]
    | .forallE n t b bi => do return Json.arr #[toJson "forallE",toJson (reprStr n),toJson (← internExpr t),toJson (← internExpr b),toJson (reprStr bi)]
    | .letE n t v b nondep => do return Json.arr #[toJson "letE",toJson (reprStr n),toJson (← internExpr t),toJson (← internExpr v),toJson (← internExpr b),toJson nondep]
    | .lit v => pure <| Json.arr #[toJson "literal",toJson (reprStr v)]
    | .mdata m b => do return Json.arr #[toJson "mdata",toJson (reprStr m),toJson (← internExpr b)]
    | .proj n i b => do return Json.arr #[toJson "proj",toJson (reprStr n),toJson i,toJson (← internExpr b)]
  let i := (← get).nodes.size
  modify fun s => {s with memo := s.memo.insert (ExprStructEq.mk e) i, nodes := s.nodes.push row}
  return i

def exprDAG (e : Expr) : Json :=
  let (root,s) := (internExpr e).run {}
  Json.mkObj [("encoding",toJson "exact-Expr-DAG-v1"),("root",toJson root),("nodes",Json.arr s.nodes)]

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
        ("body",exprDAG r.rhs)]))]
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
    ("type",exprDAG ci.type),
    ("body",match ci.value? true with | none => Json.null | some e => exprDAG e),
    ("extra",extraDetails ci), ("unsafe",toJson ci.isUnsafe),
    ("partial",toJson ci.isPartial),
    ("dependencies",toJson (deps.toList.map toString)),
    ("axioms_resolved_name_closure",toJson (axs.toList.map toString))]

def auditResolved (env : Environment) (origins : List String) : CoreM Json := do
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

def producerAudit (env : Environment) (origins : List String) : CoreM Json := do
  let resolved ← auditResolved env origins
  let mut storedAxioms : Std.HashSet Name := {}
  let mut owners : Std.HashMap Name (Array (String × String)) := {}
  for h : idx in [:env.header.moduleData.size] do
    let producer := toString env.header.moduleNames[idx]!
    let data := env.header.moduleData[idx]
    for ci in data.constants do
      if kindOf ci == "axiom" then storedAxioms := storedAxioms.insert ci.name
      owners := owners.insert ci.name ((owners[ci.name]?.getD #[]).push (producer, kindOf ci))
  let mut occurrences := #[]
  let mut producerCounts := #[]
  let mut extraNames := #[]
  for h : idx in [:env.header.moduleData.size] do
    let producer := toString env.header.moduleNames[idx]!
    if !origins.contains producer then continue
    let data := env.header.moduleData[idx]
    if data.constNames.size != data.constants.size then
      throwError "unaligned producer name/ConstantInfo arrays: {producer}"
    producerCounts := producerCounts.push (Json.mkObj [
      ("producer",toJson producer),("stored_count",toJson data.constants.size),
      ("imports",toJson (data.imports.toList.map (fun i => toString i.module))),
      ("extra_const_names",toJson (data.extraConstNames.toList.map toString))])
    for ordinal in [:data.constants.size] do
      let ci := data.constants[ordinal]!
      let n := data.constNames[ordinal]!
      if n != ci.name then throwError "producer stored name mismatch: {producer}"
      let actual ← record producer n ci
      let resolvedOrigin := (env.getModuleIdxFor? n).map (fun i => toString env.header.moduleNames[i.toNat]!)
      let resolvedInfo := env.find? n
      let resolvedRecord ← match resolvedInfo with
        | some c => record (resolvedOrigin.getD "<no-origin>") n c
        | none => pure Json.null
      let deps := ((allExprs ci).foldl (fun ns e =>
        e.getUsedConstants.foldl (fun ns n => if ns.contains n then ns else ns.push n) ns) #[]).qsort Name.lt
      let directResolvedAX := deps.filter (fun d => (env.find? d).any (fun c => kindOf c == "axiom"))
      let directStoredAX := deps.filter (storedAxioms.contains ·)
      let unresolved := deps.filter (fun d => (env.find? d).isNone)
      let dependencyOwners := deps.map fun d => Json.mkObj [
        ("name",toJson (toString d)),
        ("resolved_origin",toJson ((env.getModuleIdxFor? d).map (fun i => toString env.header.moduleNames[i.toNat]!))),
        ("stored_producers",Json.arr ((owners[d]?.getD #[]).map fun (p,k) =>
          Json.mkObj [("producer",toJson p),("kind",toJson k)]))]
      occurrences := occurrences.push (Json.mkObj [
        ("producer",toJson producer),("ordinal",toJson ordinal),("name",toJson (toString n)),
        ("actual",actual),("resolved_origin",toJson resolvedOrigin),("resolved",resolvedRecord),
        ("actual_equals_resolved_info",toJson (resolvedInfo.any (fun c => c == ci))),
        ("actual_is_direct_axiom",toJson (kindOf ci == "axiom")),
        ("directAX_resolved",toJson (directResolvedAX.toList.map toString)),
        ("directAX_any_stored_producer",toJson (directStoredAX.toList.map toString)),
        ("unresolved_dependencies",toJson (unresolved.toList.map toString)),
        ("dependency_producer_map",Json.arr dependencyOwners)])
    for n in data.extraConstNames do
      extraNames := extraNames.push (Json.mkObj [("producer",toJson producer),
        ("name",toJson (toString n)),("resolved_present",toJson ((env.find? n).isSome))])
  return Json.mkObj [
    ("schema",toJson "fresh-stored-producer-occurrences-v1"),
    ("requested_producers",toJson origins),("producer_counts",Json.arr producerCounts),
    ("occurrence_count",toJson occurrences.size),("occurrences",Json.arr occurrences),
    ("extra_names",Json.arr extraNames),("resolved_inventory",resolved)]

def main (args : List String) : IO UInt32 := do
  if args.length < 3 then
    IO.eprintln "usage: --run origin_audit.lean IMPORT_ROOT OUTPUT ORIGIN..."
    return 2
  initSearchPath (← findSysroot)
  let env ← importModules #[{module := args[0]!.toName}] {}
  let json ← (producerAudit env (args.drop 2)).toIO'
      {fileName := "<fresh-origin-audit>",fileMap := default, maxRecDepth := 1000000}
      {env := env.setExporting false}
  IO.FS.writeFile args[1]! (json.pretty ++ "\n")
  IO.println s!"inventory written: {args[1]!}"
  return 0
