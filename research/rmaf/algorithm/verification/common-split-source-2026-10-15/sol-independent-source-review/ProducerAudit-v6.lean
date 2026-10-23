import Lean
open Lean
namespace ProducerAudit

def js (s : String) : Json := Json.str s
def ja (a : Array Json) : Json := Json.arr a
def jn (n : Nat) : Json := toJson n
def jb (b : Bool) : Json := toJson b
partial def nameJson : Name → Json
  | .anonymous => ja #[js "anonymous"]
  | .str p s => ja #[js "str", nameJson p, js s]
  | .num p n => ja #[js "num", nameJson p, jn n]
partial def levelJson : Level → Json
  | .zero => ja #[js "zero"]
  | .succ u => ja #[js "succ", levelJson u]
  | .max u v => ja #[js "max", levelJson u, levelJson v]
  | .imax u v => ja #[js "imax", levelJson u, levelJson v]
  | .param n => ja #[js "param",nameJson n]
  | .mvar n => ja #[js "mvar",nameJson n.name]
def substringJson (s : Substring.Raw) : Json :=
  ja #[js s.str, jn s.startPos.byteIdx, jn s.stopPos.byteIdx]
def infoJson : SourceInfo → Json
  | .none => ja #[js "none"]
  | .synthetic p q c => ja #[js "synthetic",jn p.byteIdx,jn q.byteIdx,jb c]
  | .original a p b q => ja #[js "original",substringJson a,jn p.byteIdx,substringJson b,jn q.byteIdx]
def preJson : Syntax.Preresolved → Json
  | .namespace n => ja #[js "namespace",nameJson n]
  | .decl n fs => ja #[js "decl",nameJson n,toJson fs]
partial def syntaxJson : Syntax → Json
  | .missing => ja #[js "missing"]
  | .node i k a => ja #[js "node",infoJson i,nameJson k,ja (a.map syntaxJson)]
  | .atom i v => ja #[js "atom",infoJson i,js v]
  | .ident i r v p => ja #[js "ident",infoJson i,substringJson r,nameJson v,ja (p.toArray.map preJson)]
def dataJson : DataValue → Json
  | .ofString s => ja #[js "string",js s]
  | .ofBool b => ja #[js "bool",jb b]
  | .ofName n => ja #[js "name",nameJson n]
  | .ofNat n => ja #[js "nat",jn n]
  | .ofInt n => ja #[js "int",toJson n]
  | .ofSyntax s => ja #[js "syntax",syntaxJson s]
def binderJson : BinderInfo → Json
  | .default => js "default"
  | .implicit => js "implicit"
  | .strictImplicit => js "strictImplicit"
  | .instImplicit => js "instImplicit"
structure EncState where
  nodes : Array Json := #[]
  byContent : Std.HashMap String Nat := {}
  byPointer : Std.HashMap USize Nat := {}
-- Pointer memoization is detector infrastructure, not a mathematical proof.
-- Each ConstantInfo retains all roots during encoding; no pointed node can die.
-- Canonical interning still uses the complete tagged JSON content, not Expr BEq.
unsafe def exprJson (e : Expr) : StateM EncState Nat := do
  let addr := ptrAddrUnsafe e
  if let some i := (← get).byPointer[addr]? then return i
  let j ← match e with
    | .bvar i => pure <| ja #[js "bvar",jn i]
    | .fvar i => pure <| ja #[js "fvar",nameJson i.name]
    | .mvar i => pure <| ja #[js "mvar",nameJson i.name]
    | .sort u => pure <| ja #[js "sort",levelJson u]
    | .const n us => pure <| ja #[js "const",nameJson n,ja (us.toArray.map levelJson)]
    | .app f a => do pure <| ja #[js "app",jn (← exprJson f),jn (← exprJson a)]
    | .lam n t b bi => do pure <| ja #[js "lam",nameJson n,jn (← exprJson t),jn (← exprJson b),binderJson bi]
    | .forallE n t b bi => do pure <| ja #[js "forall",nameJson n,jn (← exprJson t),jn (← exprJson b),binderJson bi]
    | .letE n t v b nondep => do pure <| ja #[js "let",nameJson n,jn (← exprJson t),jn (← exprJson v),jn (← exprJson b),jb nondep]
    | .lit (.natVal n) => pure <| ja #[js "nat",jn n]
    | .lit (.strVal s) => pure <| ja #[js "string",js s]
    | .mdata d b => do pure <| ja #[js "mdata",ja (d.entries.toArray.map fun (n,v) => ja #[nameJson n,dataJson v]),jn (← exprJson b)]
    | .proj n i b => do pure <| ja #[js "proj",nameJson n,jn i,jn (← exprJson b)]
  let key := j.compress
  if let some i := (← get).byContent[key]? then
    modify fun s => { s with byPointer := s.byPointer.insert addr i }
    return i
  let i := (← get).nodes.size
  modify fun s => { nodes := s.nodes.push j,byContent := s.byContent.insert key i,byPointer := s.byPointer.insert addr i }
  return i

def kind : ConstantInfo → String
  | .axiomInfo _ => "axiom"
  | .defnInfo _ => "definition"
  | .thmInfo _ => "theorem"
  | .opaqueInfo _ => "opaque"
  | .quotInfo _ => "quotient"
  | .inductInfo _ => "inductive"
  | .ctorInfo _ => "constructor"
  | .recInfo _ => "recursor"
def namesJson (ns : List Name) : Json := ja (ns.toArray.map nameJson)
def hintJson : ReducibilityHints → Json
  | .opaque => ja #[js "opaque"]
  | .abbrev => ja #[js "abbrev"]
  | .regular h => ja #[js "regular",jn h.toNat]
def details : ConstantInfo → Json
  | .defnInfo v => Json.mkObj [("all",namesJson v.all),("hints",hintJson v.hints),("safety",js (reprStr v.safety))]
  | .thmInfo v => Json.mkObj [("all",namesJson v.all)]
  | .opaqueInfo v => Json.mkObj [("all",namesJson v.all)]
  | .inductInfo v => Json.mkObj [("numParams",jn v.numParams),("numIndices",jn v.numIndices),("all",namesJson v.all),("ctors",namesJson v.ctors),("numNested",jn v.numNested),("isRec",jb v.isRec),("isReflexive",jb v.isReflexive)]
  | .ctorInfo v => Json.mkObj [("induct",nameJson v.induct),("cidx",jn v.cidx),("numParams",jn v.numParams),("numFields",jn v.numFields)]
  | .recInfo v => Json.mkObj [("all",namesJson v.all),("numParams",jn v.numParams),("numIndices",jn v.numIndices),("numMotives",jn v.numMotives),("numMinors",jn v.numMinors),("k",jb v.k)]
  | .quotInfo v => js (match v.kind with | .type => "type" | .ctor => "ctor" | .lift => "lift" | .ind => "ind")
  | .axiomInfo _ => Json.null

def refs (c : ConstantInfo) : Array Name := Id.run do
  let mut ns := c.type.getUsedConstants
  if let some v := c.value? true then ns := ns ++ v.getUsedConstants
  match c with
  | .recInfo v => for r in v.rules do ns := ns ++ r.rhs.getUsedConstants
  | .inductInfo v => ns := ns ++ v.ctors.toArray
  | _ => pure ()
  return (ns.foldl (fun (s : NameSet) n => s.insert n) {}).toArray.qsort Name.lt
unsafe def declarationJson (c : ConstantInfo) : Json := Id.run do
  let action : StateM EncState (Nat × Option Nat × Array Json) := do
    let t ← exprJson c.type
    let b ← match c.value? true with
      | some e => do pure <| some (← exprJson e)
      | none => pure none
    let mut rules := #[]
    if let .recInfo v := c then
      for r in v.rules do
        rules := rules.push <| ja #[nameJson r.ctor,jn r.nfields,jn (← exprJson r.rhs)]
    return (t,b,rules)
  let ((t,b,rules),s) := action.run {}
  return Json.mkObj [("name",nameJson c.name),("name_text",js c.name.toString),("kind",js (kind c)),("levels",namesJson c.levelParams),("unsafe",jb c.isUnsafe),("partial",jb c.isPartial),("type_root",jn t),("body_root",toJson b),("rule_roots",ja rules),("nodes",ja s.nodes),("details",details c)]

structure Walk where
  seen : NameSet := {}
  axioms : NameSet := {}
  unsafeNames : NameSet := {}
  partialNames : NameSet := {}
  missing : NameSet := {}
partial def walkName (env : Environment) (n : Name) : StateM Walk Unit := do
  if (← get).seen.contains n then return
  modify fun s => {s with seen := s.seen.insert n}
  match env.find? n with
  | none => modify fun s => {s with missing := s.missing.insert n}
  | some c =>
    if c.isUnsafe then modify fun s => {s with unsafeNames := s.unsafeNames.insert n}
    if c.isPartial then modify fun s => {s with partialNames := s.partialNames.insert n}
    if kind c == "axiom" then modify fun s => {s with axioms := s.axioms.insert n}
    for d in refs c do walkName env d

def closure (env : Environment) (c : ConstantInfo) : Json := Id.run do
  let action : StateM Walk Unit := do
    if kind c == "axiom" then modify fun s => {s with axioms := s.axioms.insert c.name}
    if c.isUnsafe then modify fun s => {s with unsafeNames := s.unsafeNames.insert c.name}
    if c.isPartial then modify fun s => {s with partialNames := s.partialNames.insert c.name}
    for d in refs c do walkName env d
  let (_,s) := action.run {}
  let arr := fun (ns : NameSet) => toJson <| (ns.toArray.qsort Name.lt).map Name.toString
  return Json.mkObj [("axioms",arr s.axioms),("unsafe",arr s.unsafeNames),("partial",arr s.partialNames),("missing",arr s.missing),("visited_names",jn s.seen.size)]

def origin (env : Environment) (n : Name) : Json :=
  match env.getModuleIdxFor? n with
  | none => Json.null
  | some i => js env.header.modules[i.toNat]!.module.toString

def moduleParts (path : System.FilePath) : IO (Array System.FilePath) := do
  let mut ps := #[path]
  for suffix in [".server", ".private"] do
    let q := System.FilePath.mk (path.toString ++ suffix)
    if ← q.pathExists then ps := ps.push q
  return ps

unsafe def encodeControls : Json := Id.run do
  let nat := mkConst ``Nat
  let zero := mkNatLit 0
  let nm1 := Name.str .anonymous "a.b"
  let nm2 := Name.str (Name.str .anonymous "a") "b"
  let exprs := #[Expr.lam `x nat (.bvar 0) .default,Expr.lam `y nat (.bvar 0) .default,
    Expr.lam `x nat (.bvar 0) .implicit,
    Expr.mdata (KVMap.empty.setNat `meta 1) zero,Expr.mdata (KVMap.empty.setNat `meta 2) zero,
    mkConst nm1,mkConst nm2,mkStrLit "ab",mkStrLit "a\\nb",
    Expr.sort (.param `u),Expr.sort (.param `v),
    Expr.mdata (KVMap.empty.setSyntax `stx (.atom .none "token")) zero,
    Expr.app (mkConst `f) zero,
    Expr.forallE `x nat (.bvar 0) .strictImplicit,
    Expr.letE `x nat zero (.bvar 0) true,
    Expr.fvar ⟨`free⟩, Expr.mvar ⟨`hole⟩,
    Expr.proj `Pair 1 zero,
    Expr.sort (.max (.succ .zero) (.imax (.param `u) (.mvar ⟨`universeHole⟩))),
    Expr.mdata (KVMap.empty.setString `s "metadata" |>.setBool `b true |>.setName `n nm1 |>.setInt `i (-2) |>.setNat `k 3 |>.setSyntax `full
      (.node (.synthetic ⟨1⟩ ⟨4⟩ true) `syntaxKind #[.missing,
        .atom (.original " ".toRawSubstring ⟨1⟩ " ".toRawSubstring ⟨4⟩) "atom",
        .ident .none "raw".toRawSubstring `actual [.namespace `Ns,.decl `decl ["field"]]])) zero]
  let action : StateM EncState (Array Nat) := exprs.mapM exprJson
  let (roots,s) := action.run {}
  return Json.mkObj [("roots",toJson roots),("nodes",ja s.nodes),("expected_distinct_roots",jn 20),("name_display_collision",jb (nm1.toString (escape := false) == nm2.toString (escape := false)))]

unsafe def run (args : List String) : IO UInt32 := do
  let out :: moduleArgs := args | throw <| IO.userError "usage: ProducerAudit <out.jsonl> <module>..."
  if moduleArgs.isEmpty then throw <| IO.userError "no producers requested"
  let some sysroot ← IO.getEnv "AUDIT_SYSROOT" | throw <| IO.userError "AUDIT_SYSROOT missing"
  initSearchPath (System.FilePath.mk sysroot)
  let requested := moduleArgs.toArray.map String.toName
  let env ← importModules (requested.map fun n => {module := n}) {} 0
  let handle ← IO.FS.Handle.mk out .write
  handle.putStrLn <| (Json.mkObj [("record",js "encoder_controls"),("schema",js "producer-dag-v2"),("value",encodeControls)]).compress
  for hi : h in [:env.header.modules.size] do
    let m := env.header.modules[h].module
    let op ← findOLean m
    let parts ← moduleParts op
    handle.putStrLn <| (Json.mkObj [("record",js "module"),("module",js m.toString),("olean_parts",toJson (parts.map System.FilePath.toString)),("requested",jb (requested.contains m))]).compress
  for m in requested do
    let op ← findOLean m
    let ps ← moduleParts op
    let raw ← readModuleDataParts ps
    for hpi : pi in [:raw.size] do
      let d := raw[pi].1
      if d.constNames.size != d.constants.size then throw <| IO.userError "stored constNames/constants length mismatch"
      handle.putStrLn <| (Json.mkObj [("record",js "producer_part"),("producer",js m.toString),("part",jn pi),("is_module",jb d.isModule),("path",js ps[pi]!.toString),("imports",toJson (d.imports.map fun i => i.module.toString)),("occurrences",jn d.constants.size),("compiler_extra_names",toJson (d.extraConstNames.map Name.toString)),("compiler_extra_body_scope",js "extra names are metadata; ConstantInfo unavailable here; no body-inspection claim")]).compress
      for ci in [:d.constants.size] do
        let c := d.constants[ci]!
        if d.constNames[ci]! != c.name then throw <| IO.userError "stored name/ConstantInfo mismatch"
        let resolved := env.find? c.name
        let mut exportedViewProof := Json.null
        if d.isModule && kind c == "axiom" && !c.isUnsafe && pi + 1 < raw.size && (ps.back!).toString.endsWith ".olean.private" then
          let some pair := raw[raw.size - 1]? | throw <| IO.userError "missing final private producer part"
          let pd := pair.1
          for wi in [:pd.constants.size] do
            let w := pd.constants[wi]!
            if let .thmInfo tv := w then
              if w.name == c.name && Expr.equal w.type c.type && w.levelParams == c.levelParams && tv.all == [c.name] then
                exportedViewProof := Json.mkObj [("producer",js m.toString),("part",jn (raw.size-1)),("index",jn wi),("stored",declarationJson w),("closure",closure env w)]
        handle.putStrLn <| (Json.mkObj [("record",js "occurrence"),("schema",js "producer-dag-v2"),("producer",js m.toString),("part",jn pi),("index",jn ci),("stored_name",js c.name.toString),("resolved_origin",origin env c.name),("stored",declarationJson c),("exported_view_proof",exportedViewProof),("resolved",match resolved with | none => Json.null | some v => declarationJson v),("direct_references",toJson ((refs c).map Name.toString)),("closure",closure env c)]).compress
  handle.flush
  return 0
end ProducerAudit
unsafe def main (args : List String) : IO UInt32 := ProducerAudit.run args
