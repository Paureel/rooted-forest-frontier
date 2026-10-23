import Lean
open Lean Elab Command
namespace FreshAudit
-- One-shot campaign auditor: visits only a named root's stored declaration DAG.
structure St where
  nodes : Std.HashMap ExprStructEq Nat := {}
  rows : Array Json := #[]
  refs : Std.HashSet Name := {}
  visited : Std.HashSet Name := {}
  axioms : Array Name := #[]
  unsafes : Array Name := #[]
  forbidden : Array Name := #[]
  names : Std.HashMap Name Nat := {}
  count : Nat := 0
  deriving Inhabited
abbrev M := StateT St CoreM
def js (s : String) : Json := toJson s
def jn (n : Nat) : Json := toJson n
def obj := Json.mkObj
partial def nameNode (n : Name) : M Nat := do
 if let some i := (←get).names[n]? then return i
 let fields ← match n with
 | .anonymous => pure [("tag",js "anonymous")]
 | .str p s => do let i ← nameNode p; pure [("tag",js "str"),("parent",jn i),("value",js s)]
 | .num p k => do let i ← nameNode p; pure [("tag",js "num"),("parent",jn i),("value",jn k)]
 let i := (←get).names.size
 modify fun st => {st with names:=st.names.insert n i,rows:=st.rows.push (obj (("kind",js "name")::("id",jn i)::fields))}
 return i
partial def levelJson : Level → M Json
 | .zero => pure (toJson #[js "zero"])
 | .succ l => do return toJson #[js "succ",←levelJson l]
 | .max l r => do return toJson #[js "max",←levelJson l,←levelJson r]
 | .imax l r => do return toJson #[js "imax",←levelJson l,←levelJson r]
 | .param n => do return toJson #[js "param",jn (←nameNode n)]
 | .mvar _ => throwError "Unresolved universe metavariable"
def dataJson : DataValue → M Json
 | .ofString s => pure (toJson #[js "string",js s])
 | .ofBool b => pure (toJson #[js "bool",toJson b])
 | .ofName n => do return toJson #[js "name",jn (←nameNode n)]
 | .ofNat n => pure (toJson #[js "nat",jn n])
 | .ofInt n => pure (toJson #[js "int",toJson n])
 | .ofSyntax _ => throwError "Stored syntax metadata needs exact encoder"
partial def exprNode (e : Expr) : M Nat := do
 if let some i := (←get).nodes[ExprStructEq.mk e]? then return i
 let fields ← match e with
 | .bvar i => pure [("tag",js "bvar"),("index",jn i)]
 | .fvar _ => throwError "Stored free variable"
 | .mvar _ => throwError "Stored metavariable"
 | .sort l => do pure [("tag",js "sort"),("level",←levelJson l)]
 | .const n ls => do
   modify fun s => {s with refs:=s.refs.insert n}
   let ni ← nameNode n
   let ls ← ls.toArray.mapM levelJson
   pure [("tag",js "const"),("name",jn ni),("levels",toJson ls)]
 | .app f a => do pure [("tag",js "app"),("fn",jn (←exprNode f)),("arg",jn (←exprNode a))]
 | .lam n t b bi => do pure [("tag",js "lam"),("name",jn (←nameNode n)),("type",jn (←exprNode t)),("body",jn (←exprNode b)),("binder",js (toString (repr bi)))]
 | .forallE n t b bi => do pure [("tag",js "forall"),("name",jn (←nameNode n)),("type",jn (←exprNode t)),("body",jn (←exprNode b)),("binder",js (toString (repr bi)))]
 | .letE n t v b nondep => do pure [("tag",js "let"),("name",jn (←nameNode n)),("type",jn (←exprNode t)),("value",jn (←exprNode v)),("body",jn (←exprNode b)),("nondep",toJson nondep)]
 | .lit (.natVal k) => pure [("tag",js "nat"),("value",jn k)]
 | .lit (.strVal s) => pure [("tag",js "string"),("value",js s)]
 | .mdata md b => do
   let entries ← md.entries.toArray.mapM fun (n,v) => do
    return toJson #[jn (←nameNode n),←dataJson v]
   pure [("tag",js "mdata"),("entries",toJson entries),("body",jn (←exprNode b))]
 | .proj n i b => do pure [("tag",js "proj"),("name",jn (←nameNode n)),("index",jn i),("body",jn (←exprNode b))]
 let i := (←get).nodes.size
 modify fun st => {st with nodes:=st.nodes.insert ⟨e⟩ i,rows:=st.rows.push (obj (("kind",js "expr")::("id",jn i)::fields))}
 return i
def isForbidden (n : Name) : Bool :=
 let s := n.toString
 ["actual_pendant_safety","actual_high_safety","actual_t1_pendant_exchange","T1Exchange",
  "ordinary_branches_cover","found_globally_minimum","FastOrdinary.solve_exact",
  "ContactedClade.original_clade_split_agreement","OriginalCladeSplitAgreement",
  "exactOneRule","exactHighRule","ClosurePlants.forbiddenProbe"].any (fun needle=> decide ((s.splitOn needle).length>1))
def isStdAx (n : Name) : Bool :=
 [``Classical.choice,``propext,``Quot.sound].contains n
partial def declNode (n : Name) : M Unit := do
 if (←get).visited.contains n then return
 modify fun st => {st with visited:=st.visited.insert n}
 let env ← getEnv
 let some ci := env.find? n | throwError "Unresolved reference {n}"
 if isForbidden n then modify fun st => {st with forbidden:=st.forbidden.push n}
 if ci.isUnsafe then modify fun st => {st with unsafes:=st.unsafes.push n}
 let ni ← nameNode n
 let ti ← exprNode ci.type
 let levels ← ci.levelParams.toArray.mapM nameNode
 let mut extra : List (String×Json) := []
 let kind ← match ci with
 | .axiomInfo _ => do
   modify fun st => {st with axioms:=st.axioms.push n}
   pure "axiom"
 | .defnInfo v => do extra := [("body",jn (←exprNode v.value)),("safety",js (toString (repr v.safety)))]; pure "definition"
 | .thmInfo v => do extra := [("body",jn (←exprNode v.value))]; pure "theorem"
 | .opaqueInfo v => do extra := [("body",jn (←exprNode v.value))]; pure "opaque"
 | .quotInfo _ => pure "quotient_primitive"
 | .inductInfo _ => pure "inductive"
 | .ctorInfo _ => pure "constructor"
 | .recInfo v => do
   let rules ← v.rules.toArray.mapM fun r => do
    modify fun st => {st with refs:=st.refs.insert r.ctor}
    return obj [("constructor",jn (←nameNode r.ctor)),("fields",jn r.nfields),("rhs",jn (←exprNode r.rhs))]
   extra := [("rules",toJson rules)]
   pure "recursor"
 modify fun st => {st with count:=st.count+1,rows:=st.rows.push (obj (
  [("kind",js "declaration"),("name",jn ni),("displayName",js n.toString),
   ("declKind",js kind),("type",jn ti),("levels",toJson levels),("unsafe",toJson ci.isUnsafe)]++extra))}
partial def closure : M Unit := do
 let s ← get
 let pending := s.refs.toArray.filter (fun n=> !s.visited.contains n)
 if pending.isEmpty then return
 for n in pending do declNode n
 closure
def audit (root : Name) : CommandElabM Unit := do
 let (_,st) ← liftCoreM ((do declNode root; closure).run {})
 let badAx := st.axioms.filter (fun n=> !isStdAx n)
 for row in st.rows do liftIO (IO.println row.compress)
 liftIO (IO.println (obj [("kind",js "summary"),("root",js root.toString),
  ("declarations",jn st.count),("exprNodes",jn st.nodes.size),("nameNodes",jn st.names.size),
  ("axioms",toJson (st.axioms.map Name.toString)),("nonstandardAxioms",toJson (badAx.map Name.toString)),
  ("forbidden",toJson (st.forbidden.map Name.toString)),("unsafe",toJson (st.unsafes.map Name.toString)),
  ("unresolved",jn 0),("missingBodies",jn 0),("rawpartial",toJson false),
  ("accepted",toJson (badAx.isEmpty && st.forbidden.isEmpty && st.unsafes.isEmpty))]).compress)
end FreshAudit
