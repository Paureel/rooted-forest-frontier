import Lean
open Lean Elab Command

namespace PrepAudit

def kind (ci : ConstantInfo) : String :=
  match ci with
  | .axiomInfo _ => "axiom"
  | .defnInfo _ => "definition"
  | .thmInfo _ => "theorem"
  | .opaqueInfo _ => "opaque"
  | .quotInfo _ => "quotient"
  | .ctorInfo _ => "constructor"
  | .recInfo _ => "recursor"
  | .inductInfo _ => "inductive"

def emit (localOnly : Bool) (wanted : String) : CommandElabM Unit := do
  let env := (← getEnv).setExporting false
  let names := env.constants.fold (fun acc n _ => acc.push n) (#[] : Array Name)
  let names := names.qsort (fun a b => a.toString < b.toString)
  let mut rows : Array Json := #[]
  for n in names do
    let idx := env.getModuleIdxFor? n
    let origin := match idx with
      | none => env.mainModule
      | some i => env.allImportedModuleNames[i.toNat]!
    if origin.toString == wanted && (!localOnly || idx.isNone) then
      let some ci := env.find? n | throwError "missing inventoried declaration {n}"
      let axs ← Lean.collectAxioms n
      rows := rows.push (Json.mkObj [
        ("name", toJson n.toString),
        ("origin", toJson origin.toString),
        ("kind", toJson (kind ci)),
        ("private", toJson (Lean.privateToUserName? n).isSome),
        ("user_name", toJson ((Lean.privateToUserName? n).getD n).toString),
        ("axioms", toJson (axs.toList.map Name.toString))])
  let j := Json.mkObj [("requested_origin",toJson wanted), ("local_source_pass",toJson localOnly),
    ("declarations",Json.arr rows), ("count",toJson rows.size)]
  liftIO <| IO.println ("AUDIT_JSON " ++ j.compress)

end PrepAudit

elab "audit_local " mod:str : command => PrepAudit.emit true mod.getString
elab "audit_import " mod:str : command => PrepAudit.emit false mod.getString
