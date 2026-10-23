import ProviderResumeControls
import Lean
open Lean Elab Command
run_cmd do
 let env ← getEnv
 let wanted : List Name := [`RMAF, `ForestColorWork]
 let allowed : List Name := [`Classical.choice,`Quot.sound,`propext]
 let mut counts : Array Json := #[]
 let mut bad : Array Json := #[]
 for i in [:env.header.moduleNames.size] do
  let producer := env.header.moduleNames[i]!
  if wanted.contains producer then
   let data := env.header.moduleData[i]!
   unless data.constants.size == data.constNames.size do throwError "PRODUCER_ARRAY_LENGTH_MISMATCH"
   let mut rows : Array Json := #[]
   let path ← liftIO <| findOLean producer
   counts := counts.push (Json.mkObj [("producer",toJson producer.toString),("count",toJson data.constants.size),("path",toJson path.toString)])
   for j in [:data.constants.size] do
    let ci := data.constants[j]!
    unless data.constNames[j]! == ci.name do throwError "PRODUCER_NAME_MISMATCH"
    let kind := match ci with
     | .axiomInfo _ => "axiom" | .defnInfo _ => "definition" | .thmInfo _ => "theorem"
     | .opaqueInfo _ => "opaque" | .quotInfo _ => "quotient" | .ctorInfo _ => "constructor"
     | .recInfo _ => "recursor" | .inductInfo _ => "inductive"
    let body := match ci with | .thmInfo _ => none | _ => ci.value? true
    let mut refs := ci.getUsedConstantsAsSet.toList
    if let some e := body then refs := refs ++ e.getUsedConstants.toList
    refs := refs.eraseDups
    let mut ax : List Name := []
    if ci.isAxiom then ax := [ci.name]
    for n in refs do ax := ax ++ (← collectAxioms n).toList
    ax := ax.eraseDups
    let resolved := match env.getModuleIdxFor? ci.name with | some k => env.header.moduleNames[k.toNat]!.toString | none => "<unresolved>"
    rows := rows.push (Json.mkObj [("producer",toJson producer.toString),("index",toJson j),("name",toJson ci.name.toString),("resolved_origin",toJson resolved),("kind",toJson kind),("type",toJson (reprStr ci.type)),("body",toJson (body.map reprStr)),("body_scope",toJson (match ci with | .thmInfo _ => "OMITTED_THEOREM_TEXT_FULL_ACTUAL_PROOF_AX_WALK" | _ => "FULL_NONPROOF_BODY")),("references",toJson (refs.map Name.toString)),("axiom_references",toJson (ax.map Name.toString))])
    if (ci.isAxiom && !allowed.contains ci.name) || ax.any (fun n => !allowed.contains n) then bad := bad.push (toJson ci.name.toString)
   let payload := (Json.arr rows).compress
   if payload.utf8ByteSize > 8388608 then throwError m!"PRODUCER_OUTPUT_CAP|{producer}|{payload.utf8ByteSize}"
   let compressed ← liftIO <| IO.Process.output {cmd := "/bin/sh", args := #["-c", "exec /usr/bin/gzip -1 -c > /Users/paurel/Documents/ChatGPT/bootscience/results/algorithm-universal233-binary-resume-20261016T083330Z-final-20261016T085734Z/datatype-audit-1792141230214679000/" ++ producer.toString ++ ".json.gz"]} (some payload)
   unless compressed.exitCode == 0 do throwError "GZIP_SINK_FAILED"
 liftIO <| IO.FS.writeFile "/Users/paurel/Documents/ChatGPT/bootscience/results/algorithm-universal233-binary-resume-20261016T083330Z-final-20261016T085734Z/datatype-audit-1792141230214679000/index.json" (Json.mkObj [("counts",Json.arr counts),("rejects",Json.arr bad)]).compress
 if !bad.isEmpty then throwError m!"REJECT_PRODUCER_OCCURRENCE|{bad.size}"
 logInfo m!"PRODUCER_PASS|{counts.size}"
