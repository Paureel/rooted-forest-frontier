import Lean
open Lean Elab Command
namespace ReleasedAudit

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
    let some ci := env.find? n | throwError "missing declaration {n}"
    let axs ← Lean.collectAxioms n
    rows := rows.push (Json.mkObj [("name",toJson n.toString),("origin",toJson origin.toString),
      ("kind",toJson (kind ci)),("private",toJson (Lean.privateToUserName? n).isSome),
      ("user_name",toJson ((Lean.privateToUserName? n).getD n).toString),
      ("axioms",toJson (axs.toList.map Name.toString))])
  liftIO <| IO.println ("AUDIT_JSON " ++ (Json.mkObj [("requested_origins",toJson wanted),("declarations",Json.arr rows),("count",toJson rows.size)]).compress)
end ReleasedAudit
