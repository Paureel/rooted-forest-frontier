import NumericControls
import Lean
open Lean Elab Command
run_cmd do
  let env ← getEnv
  let wanted : List Name := [`NumericEntries]
  let allowed : List Name := [`Classical.choice,`Quot.sound,`propext]
  let mut counts : Array Json := #[]
  let mut bad : Array Json := #[]
  for i in [:env.header.moduleNames.size] do
    let producer := env.header.moduleNames[i]!
    if wanted.contains producer then
      let data := env.header.moduleData[i]!
      unless data.constants.size == data.constNames.size do throwError "PRODUCER_ARRAY_LENGTH_MISMATCH"
      let mut rows : Array Json := #[]
      let filename := producer.toString ++ ".json.gz"
      counts := counts.push (Json.mkObj [("producer",toJson producer.toString),("count",toJson data.constants.size),("file",toJson filename)])
      for j in [:data.constants.size] do
        let ci := data.constants[j]!
        let stored := data.constNames[j]!
        unless stored == ci.name do throwError "PRODUCER_NAME_MISMATCH"
        let kind := match ci with
          | .axiomInfo _ => "axiom"
          | .defnInfo _ => "definition"
          | .thmInfo _ => "theorem"
          | .opaqueInfo _ => "opaque"
          | .quotInfo _ => "quotient"
          | .ctorInfo _ => "constructor"
          | .recInfo _ => "recursor"
          | .inductInfo _ => "inductive"
        let body := ci.value? true
        let bodyText := match body with | some e => reprStr e | none => "<none>"
        let mut refs := ci.getUsedConstantsAsSet.toList
        if let some e := body then refs := refs ++ e.getUsedConstants.toList
        refs := refs.eraseDups
        let mut ax : List Name := []
        if ci.isAxiom then ax := [ci.name]
        for n in refs do ax := ax ++ (← collectAxioms n).toList
        ax := ax.eraseDups
        let resolved := match env.getModuleIdxFor? ci.name with
          | some k => env.header.moduleNames[k.toNat]!.toString
          | none => "<unresolved>"
        rows := rows.push (Json.mkObj [("producer",toJson producer.toString),("index",toJson j),
          ("stored_name",toJson stored.toString),("actual_name",toJson ci.name.toString),
          ("resolved_origin",toJson resolved),("kind",toJson kind),
          ("type",toJson (reprStr ci.type)),("body",toJson bodyText),("has_body",toJson (ci.value? true).isSome),("body_text_scope",toJson ("FULL_ALL_BODY")),
          ("direct_references",toJson (refs.map Name.toString)),("axiom_references",toJson (ax.map Name.toString))])
        if (ci.isAxiom && !allowed.contains ci.name) || ax.any (fun n => !allowed.contains n) then
          bad := bad.push (Json.mkObj [("producer",toJson producer.toString),("name",toJson ci.name.toString),("kind",toJson kind),("axioms",toJson (ax.map Name.toString))])
      let compressed ← liftIO <| IO.Process.output {cmd := "/bin/sh", args := #["-c", "exec /usr/bin/gzip -1 -c > /Users/paurel/Documents/ChatGPT/bootscience/research/rmaf/algorithm/universal233/ordinary_dispatch/global_numeric_invariants_20261016T095230Z/author-audit-v2/records-Own7/" ++ filename]} (some (Json.arr rows).pretty)
      unless compressed.exitCode == 0 do throwError "COMPRESSED_SINK_FAILED"
  liftIO <| IO.FS.writeFile ("/Users/paurel/Documents/ChatGPT/bootscience/research/rmaf/algorithm/universal233/ordinary_dispatch/global_numeric_invariants_20261016T095230Z/author-audit-v2/records-Own7" ++ "/index.json") (Json.mkObj [("producer_counts",Json.arr counts),("rejects",Json.arr bad)]).pretty
  if !bad.isEmpty then throwError m!"REJECT_PRODUCER_OCCURRENCE|{bad.size}"
  logInfo m!"PRODUCER_OCCURRENCE_PASS|{counts.size}"
