import Lean
/-! Fresh one-shot stored-producer recorder. Trusts Lean 4.35.0 APIs/IO.
Reads ModuleData.constants before Env.find? coalescence, including unused
and private producers; records full type/body/rule expression DAGs.
No author or peer detector code is imported. -/
open Lean Elab Command
namespace IndependentProducer

def arr (xs : List Json) : Json := .arr xs.toArray
def str := Json.str
def num (n : Nat) : Json := toJson n

def nameJson : Name → Json
  | .anonymous => arr [str "anonymous"]
  | .str p s => arr [str "str", nameJson p, str s]
  | .num p n => arr [str "num", nameJson p, num n]

def levelJson : Level → Json
  | .zero => arr [str "zero"]
  | .succ l => arr [str "succ", levelJson l]
  | .max a b => arr [str "max", levelJson a, levelJson b]
  | .imax a b => arr [str "imax", levelJson a, levelJson b]
  | .param n => arr [str "param", nameJson n]
  | .mvar n => arr [str "mvar", nameJson n.name]

def dataJson : DataValue → Except String Json
  | .ofString x => .ok (arr [str "string",str x])
  | .ofBool x => .ok (arr [str "bool",toJson x])
  | .ofName x => .ok (arr [str "name",nameJson x])
  | .ofNat x => .ok (arr [str "nat",num x])
  | .ofInt x => .ok (arr [str "int",toJson x])
  | .ofSyntax _ => .error "unsupported Syntax-valued Expr metadata; fail closed"

structure Dag where
  nodes : Array Json := #[]
  seen : Std.HashMap ExprStructEq Nat := {}
  refs : Std.HashSet Name := {}

abbrev Build := StateT Dag (Except String)

partial def encode (e : Expr) : Build Nat := do
  if let some index := (← get).seen[ExprStructEq.mk e]? then
    return index
  let node ← match e with
    | .bvar n => pure (arr [str "bvar",num n])
    | .fvar id => pure (arr [str "fvar",nameJson id.name])
    | .mvar id => pure (arr [str "mvar",nameJson id.name])
    | .sort l => pure (arr [str "sort",levelJson l])
    | .const n ls => do
        modify fun s => { s with refs := s.refs.insert n }
        pure (arr [str "const",nameJson n,.arr (ls.map levelJson).toArray])
    | .app f a => do
        let fi ← encode f
        let ai ← encode a
        pure (arr [str "app",num fi,num ai])
    | .lam n t b bi => do
        let ti ← encode t
        let bidx ← encode b
        pure (arr [str "lam",nameJson n,num ti,num bidx,str (reprStr bi)])
    | .forallE n t b bi => do
        let ti ← encode t
        let bidx ← encode b
        pure (arr [str "forall",nameJson n,num ti,num bidx,str (reprStr bi)])
    | .letE n t v b nondep => do
        let ti ← encode t
        let vi ← encode v
        let bidx ← encode b
        pure (arr [str "let",nameJson n,num ti,num vi,num bidx,toJson nondep])
    | .lit (.natVal n) => pure (arr [str "nat",num n])
    | .lit (.strVal s) => pure (arr [str "string",str s])
    | .mdata md b => do
        let mut entries := #[]
        for (n,v) in md.entries do
          let j ← match dataJson v with
            | .ok j => pure j
            | .error message => throw message
          entries := entries.push (arr [nameJson n,j])
        let bi ← encode b
        pure (arr [str "mdata",.arr entries,num bi])
    | .proj n i b => do
        let bi ← encode b
        pure (arr [str "proj",nameJson n,num i,num bi])
  let index := (← get).nodes.size
  modify fun s => { s with nodes := s.nodes.push node, seen := s.seen.insert { val := e } index }
  return index

def expression (e : Expr) : Except String Json := do
  let (root,s) ← (encode e).run {}
  let refs := s.refs.toList.map Name.toString |>.mergeSort (· ≤ ·)
  return Json.mkObj [("root",num root),("nodes",.arr s.nodes),("refs",toJson refs)]

def kind : ConstantInfo → String
  | .axiomInfo _ => "axiom"
  | .defnInfo _ => "definition"
  | .thmInfo _ => "theorem"
  | .opaqueInfo _ => "opaque"
  | .quotInfo _ => "quotient"
  | .inductInfo _ => "inductive"
  | .ctorInfo _ => "constructor"
  | .recInfo _ => "recursor"

def extra (c : ConstantInfo) : Json :=
  match c with
  | .defnInfo d =>
      let hints := match d.hints with
        | .opaque => arr [str "opaque"]
        | .abbrev => arr [str "abbrev"]
        | .regular n => arr [str "regular",num n.toNat]
      Json.mkObj [("safety",str (reprStr d.safety)),("hints",hints),("all",toJson (d.all.map Name.toString))]
  | .opaqueInfo d => Json.mkObj [("unsafe",toJson d.isUnsafe),("all",toJson (d.all.map Name.toString))]
  | .recInfo d => Json.mkObj [("unsafe",toJson d.isUnsafe),("all",toJson (d.all.map Name.toString)),("params",num d.numParams),("indices",num d.numIndices),("motives",num d.numMotives),("minors",num d.numMinors),("k",toJson d.k)]
  | _ => .null

def record (c : ConstantInfo) : Except String Json := do
  let t ← expression c.type
  let body ← match c.value? (allowOpaque := true) with
    | none => pure Json.null
    | some b => expression b
  let mut rules := #[]
  if let .recInfo r := c then
    for rule in r.rules do
      let rhs ← expression rule.rhs
      rules := rules.push (Json.mkObj [("ctor",nameJson rule.ctor),("nfields",num rule.nfields),("rhs",rhs)])
  return Json.mkObj [("name",str c.name.toString),("structural_name",nameJson c.name),
    ("kind",str (kind c)),("level_params",.arr (c.levelParams.map nameJson).toArray),
    ("type",t),("body",body),("rules",.arr rules),("extra",extra c)]

def emit (j : Json) : CommandElabM Unit := liftIO <| IO.println ("PRODUCER " ++ j.compress)

elab "audit_producers " pref:str : command => do
  let env ← getEnv
  let p := pref.getString
  let mut count := 0
  let mut names : Std.HashSet Name := {}
  for i in [:env.header.moduleData.size] do
    let moduleName := env.header.modules[i]!.module
    if moduleName.toString.startsWith p then
      let data := env.header.moduleData[i]!
      for j in [:data.constants.size] do
        let c := data.constants[j]!
        let r ← match record c with
          | .ok r => pure r
          | .error error => throwError "producer {moduleName}:{j} {c.name}: {error}"
        emit <| Json.mkObj [("layer",str "raw-module"),("module",str moduleName.toString),
          ("module_index",num i),("producer_index",num j),("declared_name_count",num data.constNames.size),
          ("extra_names",toJson (data.extraConstNames.toList.map Name.toString)),("producer",r)]
        names := names.insert c.name
        count := count+1
  for n in names.toList.mergeSort (fun a b => a.toString ≤ b.toString) do
    let some c := env.find? n | throwError "raw producer absent after import: {n}"
    let r ← match record c with
      | .ok r => pure r
      | .error error => throwError "coalesced {n}: {error}"
    let origin := match env.getModuleIdxFor? n with
      | none => "current-or-unresolved"
      | some i => env.header.modules[i]!.module.toString
    emit <| Json.mkObj [("layer",str "coalesced"),("origin",str origin),("producer",r)]
  emit <| Json.mkObj [("layer",str "summary"),("raw_occurrences",num count),("distinct_names",num names.size)]
end IndependentProducer
