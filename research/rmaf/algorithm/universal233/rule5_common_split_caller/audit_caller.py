"""Stored producer audit, adapted from the completed Rule4 author instrument.

Author DEVELOPMENT reuse, not an independent verification. Split producer
files avoid retaining every pretty-printed proof body in one huge JSON value.
Full exact ConstantInfo fields remain in the per-producer evidence.
"""
from __future__ import annotations
import json

ALLOWED = {"Classical.choice", "Quot.sound", "propext"}

def audit_source(imports, modules, directory):
    quote=lambda x:json.dumps(str(x))
    wanted=", ".join("`"+x for x in modules)
    return "\n".join("import "+x for x in imports)+'''\nimport Lean
open Lean Elab Command
run_cmd do
  let env ← getEnv
  let wanted : List Name := ['''+wanted+''']
  let allowed : List Name := [`Classical.choice,`Quot.sound,`propext]
  let mut counts : Array Json := #[]
  let mut bad : Array Json := #[]
  for i in [:env.header.moduleNames.size] do
    let producer := env.header.moduleNames[i]!
    if wanted.contains producer then
      let data := env.header.moduleData[i]!
      unless data.constants.size == data.constNames.size do throwError "PRODUCER_ARRAY_LENGTH_MISMATCH"
      let mut rows : Array Json := #[]
      let filename := producer.toString ++ ".json"
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
        let mut refs := ci.type.getUsedConstants.toList
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
          ("type",toJson (reprStr ci.type)),("body",toJson bodyText),("has_body",toJson body.isSome),
          ("direct_references",toJson (refs.map Name.toString)),("axiom_references",toJson (ax.map Name.toString))])
        if (ci.isAxiom && !allowed.contains ci.name) || ax.any (fun n => !allowed.contains n) then
          bad := bad.push (Json.mkObj [("producer",toJson producer.toString),("name",toJson ci.name.toString),("kind",toJson kind),("axioms",toJson (ax.map Name.toString))])
      liftIO <| IO.FS.writeFile ('''+quote(directory)+''' ++ "/" ++ filename) (Json.arr rows).pretty
  liftIO <| IO.FS.writeFile ('''+quote(directory)+''' ++ "/index.json") (Json.mkObj [("producer_counts",Json.arr counts),("rejects",Json.arr bad)]).pretty
  if !bad.isEmpty then throwError m!"REJECT_PRODUCER_OCCURRENCE|{bad.size}"
  logInfo m!"PRODUCER_OCCURRENCE_PASS|{counts.size}"
'''

def parse_producer(count, rows, expect_reject=False):
    assert len(rows)==count["count"], "MISSING_OCCURRENCE"
    assert [r["index"] for r in rows]==list(range(count["count"])), "DUPLICATE_OR_MISSING_OCCURRENCE"
    assert len({r["stored_name"] for r in rows})==len(rows), "DUPLICATE_PRODUCER_NAME"
    for r in rows:
        assert r["producer"]==count["producer"], "PRODUCER_ATTRIBUTION"
        assert r["stored_name"]==r["actual_name"], "ACTUAL_NAME"
        assert r["resolved_origin"]!="<unresolved>", "UNDECIDABLE_ORIGIN"
        assert r["kind"] in {"axiom","definition","theorem","opaque","quotient","constructor","recursor","inductive"}
        assert isinstance(r["type"],str) and r["type"], "MISSING_TYPE"
        assert isinstance(r["body"],str) and r["body"], "MISSING_BODY_RECORD"
    bad=[r for r in rows if (r["kind"]=="axiom" and r["actual_name"] not in ALLOWED)
         or not set(r["axiom_references"])<=ALLOWED]
    if not expect_reject: assert not bad, "CUSTOM_PRODUCER_AXIOM"
    return bad
