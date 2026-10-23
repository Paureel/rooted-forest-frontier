import FingerprintSupport
open Lean Elab Command
namespace ProducerDataAudit

def directDeps (ci : ConstantInfo) : List Name :=
  ci.type.getUsedConstants.toList ++ ((ProducerFingerprint.value ci).map (fun e => e.getUsedConstants.toList)).getD []

def emit (wanted : List String) : CommandElabM Unit := do
  let env := (← getEnv).setExporting false
  let mut rows : Array Json := #[]
  let mut modules : Array Json := #[]
  for i in [:env.header.modules.size] do
    let origin := env.header.modules[i]!.module
    if wanted.contains origin.toString then
      let data := env.header.moduleData[i]!
      modules := modules.push (Json.mkObj [("origin",toJson origin.toString),("count",toJson data.constants.size),("stored_names",toJson (data.constNames.toList.map Name.toString))])
      for ci in data.constants do
        let n := ci.name
        let mut axs : NameSet := {}
        match ci with
        | .axiomInfo _ => axs := axs.insert n
        | _ => pure ()
        for dep in directDeps ci do
          for ax in (← Lean.collectAxioms dep) do
            axs := axs.insert ax
        let resolvedOrigin := match env.getModuleIdxFor? n with
          | none => env.mainModule
          | some k => env.allImportedModuleNames[k.toNat]!
        rows := rows.push (Json.mkObj [("origin",toJson origin.toString),("resolved_origin",toJson resolvedOrigin.toString),
          ("name",toJson n.toString),("kind",toJson (ReleasedAudit.kind ci)),("private",toJson (Lean.privateToUserName? n).isSome),
          ("user_name",toJson ((Lean.privateToUserName? n).getD n).toString),
          ("axioms",toJson ((axs.toArray.qsort Name.lt).toList.map Name.toString)),
          ("type_hash64",toJson (hash (ProducerFingerprint.normalized ci.type)).toNat),
          ("value_hash64",toJson ((ProducerFingerprint.value ci).map (fun e => (hash (ProducerFingerprint.normalized e)).toNat)))])
  liftIO <| IO.println ("PRODUCER_DATA_JSON " ++ (Json.mkObj [("requested_origins",toJson wanted),("modules",Json.arr modules),("declarations",Json.arr rows),("count",toJson rows.size)]).compress)
end ProducerDataAudit
