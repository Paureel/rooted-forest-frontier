import OriginAudit
open Lean Elab Command
namespace ProducerFingerprint

def normalized : Expr → Expr
  | .bvar i => .bvar i
  | .fvar i => .fvar i
  | .mvar i => .mvar i
  | .sort l => .sort l
  | .const n ls => .const ((Lean.privateToUserName? n).getD n) ls
  | .app f a => .app (normalized f) (normalized a)
  | .lam _ t b bi => .lam Name.anonymous (normalized t) (normalized b) bi
  | .forallE _ t b bi => .forallE Name.anonymous (normalized t) (normalized b) bi
  | .letE _ t v b nd => .letE Name.anonymous (normalized t) (normalized v) (normalized b) nd
  | .lit l => .lit l
  | .mdata d e => .mdata d (normalized e)
  | .proj n i e => .proj ((Lean.privateToUserName? n).getD n) i (normalized e)

def value (ci : ConstantInfo) : Option Expr := match ci with
  | .defnInfo v => some v.value
  | .thmInfo v => some v.value
  | .opaqueInfo v => some v.value
  | _ => none

def emit (wanted : List String) : CommandElabM Unit := do
  let env := (← getEnv).setExporting false
  let names := env.constants.fold (fun acc n _ =>
    let origin := match env.getModuleIdxFor? n with
      | none => env.mainModule
      | some i => env.allImportedModuleNames[i.toNat]!
    if wanted.contains origin.toString then acc.push n else acc) (#[] : Array Name)
  let names := names.qsort (fun a b => a.toString < b.toString)
  let mut rows : Array Json := #[]
  for n in names do
    let origin := match env.getModuleIdxFor? n with
      | none => env.mainModule
      | some i => env.allImportedModuleNames[i.toNat]!
    let some ci := env.find? n | throwError "Missing declaration {n}"
    rows := rows.push (Json.mkObj [("origin",toJson origin.toString),("name",toJson n.toString),
      ("user_name",toJson ((Lean.privateToUserName? n).getD n).toString),("private",toJson (Lean.privateToUserName? n).isSome),
      ("kind",toJson (ReleasedAudit.kind ci)),("type",toJson (reprStr (normalized ci.type))),
      ("value",toJson ((value ci).map (fun e => reprStr (normalized e))))])
  liftIO <| IO.println ("FINGERPRINT_JSON " ++ (Json.arr rows).compress)
end ProducerFingerprint
