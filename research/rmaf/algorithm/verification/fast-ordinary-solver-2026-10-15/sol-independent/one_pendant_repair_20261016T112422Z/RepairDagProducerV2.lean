/- One-campaign environment producer. No candidate imports or project producer reuse.
   Actual stored expression traversal; imported precomputed axiom extensions unused.
   Proof TEXT is omitted only after walking the actual full proof expression.
   Nonproof and opaque values are serialized completely as constructor trees. -/
import Lean
open Lean

def js (s : String) : Json := Json.str s
def ja (xs : List Json) : Json := Json.arr xs.toArray

partial def nameTree : Name → Json
  | .anonymous => ja [js "anonymous"]
  | .str p s => ja [js "str",nameTree p,js s]
  | .num p n => ja [js "num",nameTree p,toJson n]

def dataTree : DataValue → Json
  | .ofString s => ja [js "string",js s]
  | .ofBool b => ja [js "bool",toJson b]
  | .ofName n => ja [js "name",nameTree n]
  | .ofNat n => ja [js "nat",toJson n]
  | .ofInt n => ja [js "int",toJson n]
  | .ofSyntax stx => ja [js "syntax-unencoded",js (reprStr stx)]

def metadataTree (md : MData) : Json :=
  ja (md.entries.map (fun (key,value) => ja [nameTree key,dataTree value]))

partial def levelTree : Level → Json
  | .zero => ja [js "zero"]
  | .succ u => ja [js "succ", levelTree u]
  | .max u v => ja [js "max", levelTree u, levelTree v]
  | .imax u v => ja [js "imax", levelTree u, levelTree v]
  | .param n => ja [js "param", js n.toString]
  | .mvar n => ja [js "mvar", js n.name.toString]

structure DagState where
 seen : Std.HashMap ExprStructEq Nat := {}
 nodes : Array Json := #[]

partial def dagVisit (e : Expr) : StateM DagState Nat := do
 if let some i := (←get).seen[(⟨e⟩ : ExprStructEq)]? then return i
 let ref (e : Expr) : StateM DagState Json := do return ja [js "ref",toJson (←dagVisit e)]
 let j : Json ← match e with
 | .bvar i=>pure (ja [js "bvar",toJson i])
 | .fvar i=>pure (ja [js "fvar",js i.name.toString])
 | .mvar i=>pure (ja [js "mvar",js i.name.toString])
 | .sort u=>pure (ja [js "sort",levelTree u])
 | .const c us=>pure (ja [js "const",js c.toString,ja (us.map levelTree)])
 | .app f x=>do pure (ja [js "app",←ref f,←ref x])
 | .lam n t b bi=>do pure (ja [js "lam",js n.toString,←ref t,←ref b,js (reprStr bi)])
 | .forallE n t b bi=>do pure (ja [js "forall",js n.toString,←ref t,←ref b,js (reprStr bi)])
 | .letE n t v b nd=>do pure (ja [js "let",js n.toString,←ref t,←ref v,←ref b,toJson nd])
 | .lit (.natVal i)=>pure (ja [js "nat",toJson i])
 | .lit (.strVal s)=>pure (ja [js "str",js s])
 | .mdata md b=>do pure (ja [js "metadata",metadataTree md,←ref b])
 | .proj c i b=>do pure (ja [js "proj",js c.toString,toJson i,←ref b])
 let i := (←get).nodes.size
 if i>=10000 then panic! "DAG node cap"
 modify fun st=>{seen:=st.seen.insert ⟨e⟩ i,nodes:=st.nodes.push j}
 return i

def exprDag (e : Expr) : Json :=
 let (i,st) := (dagVisit e).run {}
 ja [js "dag-v1",toJson i,Json.arr st.nodes]

structure ActualRefState where
  seen : Std.HashSet ExprStructEq := {}
  refs : Std.HashSet Name := {}

partial def visitActualRefs (e : Expr) : StateM ActualRefState Unit := do
  if (← get).seen.contains ⟨e⟩ then return
  modify fun s => {s with seen := s.seen.insert ⟨e⟩}
  match e with
  | .const n _ => modify fun s => {s with refs := s.refs.insert n}
  | .app a b => visitActualRefs a; visitActualRefs b
  | .lam _ t b _ | .forallE _ t b _ => visitActualRefs t; visitActualRefs b
  | .letE _ t v b _ => visitActualRefs t; visitActualRefs v; visitActualRefs b
  | .mdata _ child => visitActualRefs child
  | .proj n _ child =>
      modify fun s => {s with refs := s.refs.insert n}
      visitActualRefs child
  | _ => pure ()

def actualRefs (e : Expr) : List Name :=
  ((visitActualRefs e).run {}).2.refs.toList

partial def countActualNodes (e : Expr) : StateM (Std.HashMap ExprStructEq Nat) Nat := do
  if let some n := (← get)[(⟨e⟩ : ExprStructEq)]? then return n
  let children := match e with
    | .app a b => [a,b]
    | .lam _ t b _ | .forallE _ t b _ => [t,b]
    | .letE _ t v b _ => [t,v,b]
    | .mdata _ child | .proj _ _ child => [child]
    | _ => []
  let mut n := 1
  for child in children do
    n := n + (← countActualNodes child)
  modify fun s => s.insert ⟨e⟩ n
  return n

def actualNodes (e : Expr) : Nat := (countActualNodes e).run' {}

def kind : ConstantInfo → String
  | .axiomInfo _ => "axiom"
  | .defnInfo _ => "definition"
  | .thmInfo _ => "theorem"
  | .opaqueInfo _ => "opaque"
  | .quotInfo _ => "quotient"
  | .inductInfo _ => "inductive"
  | .ctorInfo _ => "constructor"
  | .recInfo _ => "recursor"

def uniq (ns : List Name) : List Name := (ns.eraseDups).mergeSort Name.lt

def dataPayload : ConstantInfo → Json
  | .defnInfo v => Json.mkObj [("safety",js (reprStr v.safety)),("hints",match v.hints with
      | .opaque => ja [js "opaque"] | .abbrev => ja [js "abbrev"]
      | .regular h => ja [js "regular",toJson h.toNat]),("all",toJson (v.all.map Name.toString))]
  | .thmInfo v => Json.mkObj [("all",toJson (v.all.map Name.toString))]
  | .opaqueInfo v => Json.mkObj [("all",toJson (v.all.map Name.toString))]
  | .inductInfo v => Json.mkObj [("all",toJson (v.all.map Name.toString)),
      ("ctors",toJson (v.ctors.map Name.toString)),("numParams",toJson v.numParams),
      ("numIndices",toJson v.numIndices),("numNested",toJson v.numNested),
      ("isRec",toJson v.isRec),("isReflexive",toJson v.isReflexive)]
  | .ctorInfo v => Json.mkObj [("induct",js v.induct.toString),("cidx",toJson v.cidx),
      ("numParams",toJson v.numParams),("numFields",toJson v.numFields)]
  | .recInfo v => Json.mkObj [("all",toJson (v.all.map Name.toString)),
      ("numParams",toJson v.numParams),("numIndices",toJson v.numIndices),
      ("numMotives",toJson v.numMotives),("numMinors",toJson v.numMinors),("k",toJson v.k),
      ("rules",ja (v.rules.map (fun (r : RecursorRule) => Json.mkObj [
        ("ctor",js r.ctor.toString),("nfields",toJson r.nfields),("rhs",exprDag r.rhs)])))]
  | .quotInfo v => Json.mkObj [("quotKind",js (match v.kind with
      | .type => "type" | .ctor => "ctor" | .lift => "lift" | .ind => "ind"))]
  | .axiomInfo _ => Json.mkObj []

def extraRefs : ConstantInfo → List Name
  | .inductInfo v => v.all ++ v.ctors
  | .ctorInfo v => [v.induct]
  | .recInfo v => v.all ++ v.rules.flatMap (fun (r : RecursorRule) => r.ctor :: actualRefs r.rhs)
  | _ => []

def moduleOf (env : Environment) (n : Name) : String :=
  match env.getModuleIdxFor? n with
  | some i => (env.header.moduleNames[i.toNat]!).toString
  | none => "<unmapped>"

def row (env : Environment) (ci : ConstantInfo) : Json := Id.run do
  let value := ci.value? (allowOpaque := true)
  let bodyRefs := value.map actualRefs |>.getD [] |> uniq
  let extra := uniq (extraRefs ci)
  return Json.mkObj [
    ("name", js ci.name.toString), ("module", js (moduleOf env ci.name)),
    ("kind", js (kind ci)), ("unsafe", toJson ci.isUnsafe), ("partial", toJson ci.isPartial),
    ("data_payload",dataPayload ci),
    ("levels", toJson (ci.levelParams.map Name.toString)),
    ("type", exprDag ci.type), ("type_refs", toJson ((uniq (actualRefs ci.type)).map Name.toString)),
    ("body_refs", toJson (bodyRefs.map Name.toString)), ("extra_refs", toJson (extra.map Name.toString)),
    ("body_nodes", toJson (value.map actualNodes |>.getD 0)),
    ("proof_body_omitted_after_actual_walk", toJson ci.isTheorem),
    ("body", if ci.isTheorem then Json.null else value.map exprDag |>.getD Json.null)]

def Lean.Json.boundedCompress (j : Json) : String :=
 let s := j.compress
 if s.utf8ByteSize>4*1024*1024 then panic! "DAG chunk cap" else s

def main (args : List String) : IO UInt32 := do
  initSearchPath (← findSysroot)
  let (entry, selectors) ← match args with
    | "--entry" :: e :: "--select" :: ss => pure (some e,ss)
    | _ => pure (none,args)
  if selectors.eraseDups.length != selectors.length then throw (IO.userError "duplicate selectors")
  if selectors.isEmpty then throw (IO.userError "empty selectors")
  let mods := match entry with
    | some e => [e.toName]
    | none => selectors.map String.toName
  if mods.isEmpty then throw (IO.userError "no licensed module arguments")
  let env ← importModules (mods.map (fun m => ({module := m} : Import))).toArray {}
    (trustLevel := 0) (loadExts := false) (level := .private)
  let constants := env.constants.toList
  for s in selectors do
    if !env.header.moduleNames.contains s.toName then throw (IO.userError s!"selector not loaded: {s}")
  let own := constants.filter (fun (n, _) => selectors.contains (moduleOf env n))
  let own := own.mergeSort (fun a b => Name.lt a.1 b.1)
  let stdout ← IO.getStdout
  let counts := selectors.map fun s => (s,toJson (own.filter (fun (n,_) => moduleOf env n == s)).length)
  stdout.putStrLn ((Json.mkObj [("record",js "header"),("modules",toJson selectors),
    ("fixed_entrypoint",toJson entry),("module_counts",Json.mkObj counts),
    ("count",toJson own.length),("import_level",js "private"),
    ("source",js "actual stored ConstantInfo values; no collectAxioms cache")]).boundedCompress)
  let mut external : List Name := []
  for (_,ci) in own do
    stdout.putStrLn ((row env ci).boundedCompress)
    let refs := actualRefs ci.type ++ (ci.value? true |>.map actualRefs |>.getD []) ++ extraRefs ci
    for dep in refs do
      if !selectors.contains (moduleOf env dep) then external := dep :: external
  for dep in uniq external do
    match env.checked.get.find? dep with
    | none => throw (IO.userError s!"missing referenced declaration {dep}")
    | some ci => stdout.putStrLn ((Json.mkObj [("record",js "external-trust-boundary"),
        ("name",js dep.toString),("module",js (moduleOf env dep)),("kind",js (kind ci))]).boundedCompress)
  return 0
