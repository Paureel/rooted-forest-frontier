/- One-campaign environment producer. No candidate imports or project producer reuse.
   Actual stored expression traversal; imported precomputed axiom extensions unused.
   Proof TEXT is omitted only after walking the actual full proof expression.
   Nonproof and opaque values are serialized completely as constructor trees. -/
import Lean
open Lean

def js (s : String) : Json := Json.str s
def ja (xs : List Json) : Json := Json.arr xs.toArray

partial def levelTree : Level → Json
  | .zero => ja [js "zero"]
  | .succ u => ja [js "succ", levelTree u]
  | .max u v => ja [js "max", levelTree u, levelTree v]
  | .imax u v => ja [js "imax", levelTree u, levelTree v]
  | .param n => ja [js "param", js n.toString]
  | .mvar n => ja [js "mvar", js n.name.toString]

partial def exprTree : Expr → Json
  | .bvar n => ja [js "bvar", toJson n]
  | .fvar n => ja [js "fvar", js n.name.toString]
  | .mvar n => ja [js "mvar", js n.name.toString]
  | .sort u => ja [js "sort", levelTree u]
  | .const n us => ja [js "const", js n.toString, ja (us.map levelTree)]
  | .app a b => ja [js "app", exprTree a, exprTree b]
  | .lam n t b bi => ja [js "lam", js n.toString, exprTree t, exprTree b, js (reprStr bi)]
  | .forallE n t b bi => ja [js "forall", js n.toString, exprTree t, exprTree b, js (reprStr bi)]
  | .letE n t v b nondep => ja [js "let", js n.toString, exprTree t, exprTree v, exprTree b, toJson nondep]
  | .lit (.natVal n) => ja [js "nat", toJson n]
  | .lit (.strVal s) => ja [js "str", js s]
  | .mdata md e => ja [js "metadata", js (reprStr md), exprTree e]
  | .proj n i e => ja [js "proj", js n.toString, toJson i, exprTree e]

partial def actualRefs : Expr → List Name
  | .const n _ => [n]
  | .app a b => actualRefs a ++ actualRefs b
  | .lam _ t b _ | .forallE _ t b _ => actualRefs t ++ actualRefs b
  | .letE _ t v b _ => actualRefs t ++ actualRefs v ++ actualRefs b
  | .mdata _ e => actualRefs e
  | .proj n _ e => n :: actualRefs e
  | _ => []

partial def actualNodes : Expr → Nat
  | .app a b => 1 + actualNodes a + actualNodes b
  | .lam _ t b _ | .forallE _ t b _ => 1 + actualNodes t + actualNodes b
  | .letE _ t v b _ => 1 + actualNodes t + actualNodes v + actualNodes b
  | .mdata _ e | .proj _ _ e => 1 + actualNodes e
  | _ => 1

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

def moduleOf (env : Environment) (n : Name) : String :=
  match env.getModuleIdxFor? n with
  | some i => (env.header.moduleNames[i.toNat]!).toString
  | none => "<unmapped>"

def row (env : Environment) (ci : ConstantInfo) : Json := Id.run do
  let value := ci.value? (allowOpaque := true)
  let bodyRefs := value.map actualRefs |>.getD [] |> uniq
  let extra := match ci with
    | .inductInfo v => v.ctors
    | .recInfo v => v.rules.map (fun (r : RecursorRule) => r.ctor)
    | _ => []
  return Json.mkObj [
    ("name", js ci.name.toString), ("module", js (moduleOf env ci.name)),
    ("kind", js (kind ci)), ("unsafe", toJson ci.isUnsafe), ("partial", toJson ci.isPartial),
    ("levels", toJson (ci.levelParams.map Name.toString)),
    ("type", exprTree ci.type), ("type_refs", toJson ((uniq (actualRefs ci.type)).map Name.toString)),
    ("body_refs", toJson (bodyRefs.map Name.toString)), ("extra_refs", toJson (extra.map Name.toString)),
    ("body_nodes", toJson (value.map actualNodes |>.getD 0)),
    ("proof_body_omitted_after_actual_walk", toJson ci.isTheorem),
    ("body", if ci.isTheorem then Json.null else value.map exprTree |>.getD Json.null)]

def main (args : List String) : IO UInt32 := do
  initSearchPath (← findSysroot)
  let mods := args.map String.toName
  if mods.isEmpty then throw (IO.userError "no licensed module arguments")
  let env ← importModules (mods.map (fun m => ({module := m} : Import))).toArray {}
    (trustLevel := 0) (loadExts := false) (level := .private)
  let constants := env.constants.toList
  let own := constants.filter (fun (n, _) => args.contains (moduleOf env n))
  let own := own.mergeSort (fun a b => Name.lt a.1 b.1)
  let stdout ← IO.getStdout
  stdout.putStrLn ((Json.mkObj [("record",js "header"),("modules",toJson args),
    ("count",toJson own.length),("import_level",js "private"),
    ("source",js "actual stored ConstantInfo values; no collectAxioms cache")]).compress)
  let mut external : List Name := []
  for (_,ci) in own do
    stdout.putStrLn ((row env ci).compress)
    let refs := actualRefs ci.type ++ (ci.value? true |>.map actualRefs |>.getD [])
    for dep in refs do
      if !args.contains (moduleOf env dep) then external := dep :: external
  for dep in uniq external do
    match env.checked.get.find? dep with
    | none => throw (IO.userError s!"missing referenced declaration {dep}")
    | some ci => stdout.putStrLn ((Json.mkObj [("record",js "external-trust-boundary"),
        ("name",js dep.toString),("module",js (moduleOf env dep)),("kind",js (kind ci))]).compress)
  return 0
