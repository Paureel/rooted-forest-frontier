#!/usr/bin/env python3
"""One-shot Rule4 producer-occurrence audit, independently implemented from
Lean's Environment/Declaration/CollectAxioms source and the root amendment.
No independent reviewer implementation was read. This is an author check.
"""
import json,re
ALLOWED={'Classical.choice','Quot.sound','propext'}

def audit_source(imports, modules, destination):
    quoted=lambda s:json.dumps(str(s))
    names=', '.join('`'+n for n in modules)
    return '\n'.join('import '+n for n in imports)+'''\nimport Lean
open Lean Elab Command
run_cmd do
  let env ← getEnv
  let wanted : List Name := ['''+names+''']
  let allowed : List Name := [`Classical.choice,`Quot.sound,`propext]
  let mut rows : Array Json := #[]
  let mut counts : Array Json := #[]
  let mut bad : Array Json := #[]
  for i in [:env.header.moduleNames.size] do
    let producer := env.header.moduleNames[i]!
    if wanted.contains producer then
      let data := env.header.moduleData[i]!
      unless data.constants.size == data.constNames.size do
        throwError "PRODUCER_ARRAY_LENGTH_MISMATCH"
      counts := counts.push (Json.mkObj [("producer",toJson producer.toString),("count",toJson data.constants.size)])
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
        let row := Json.mkObj [
          ("producer",toJson producer.toString),("index",toJson j),
          ("stored_name",toJson stored.toString),("actual_name",toJson ci.name.toString),
          ("resolved_origin",toJson resolved),("kind",toJson kind),
          ("type",toJson (reprStr ci.type)),("body",toJson bodyText),
          ("has_body",toJson body.isSome),
          ("direct_references",toJson (refs.map Name.toString)),
          ("axiom_references",toJson (ax.map Name.toString))]
        rows := rows.push row
        if (ci.isAxiom && !allowed.contains ci.name) || ax.any (fun n => !allowed.contains n) then
          bad := bad.push (Json.mkObj [("producer",toJson producer.toString),("name",toJson ci.name.toString),("kind",toJson kind),("axioms",toJson (ax.map Name.toString))])
  let result := Json.mkObj [("producer_counts",Json.arr counts),("occurrences",Json.arr rows),("rejects",Json.arr bad)]
  liftIO <| IO.FS.writeFile '''+quoted(destination)+''' result.pretty
  if !bad.isEmpty then throwError m!"REJECT_PRODUCER_OCCURRENCE|{bad.size}"
  logInfo m!"PRODUCER_OCCURRENCE_PASS|{counts.size}|{rows.size}"
'''

def parse_occurrences(data, modules, expect_reject=False):
    assert {r['producer'] for r in data['producer_counts']}==set(modules),'PRODUCER_SET'
    assert len(data['producer_counts'])==len(modules),'DUPLICATE_PRODUCER'
    rows=data['occurrences'];keys=[(r['producer'],r['index']) for r in rows]
    assert len(keys)==len(set(keys)),'DUPLICATE_OCCURRENCE'
    for count in data['producer_counts']:
        producer=count['producer'];rr=[r for r in rows if r['producer']==producer]
        assert sorted(r['index'] for r in rr)==list(range(count['count'])),'MISSING_OCCURRENCE'
        assert len({r['stored_name'] for r in rr})==len(rr),'DUPLICATE_PRODUCER_NAME'
    for row in rows:
        assert row['stored_name']==row['actual_name'],'ACTUAL_NAME'
        assert row['resolved_origin']!='<unresolved>','UNDECIDABLE_ORIGIN'
        assert row['kind'] in {'axiom','definition','theorem','opaque','quotient','constructor','recursor','inductive'}
        assert isinstance(row['type'],str) and row['type'],'MISSING_TYPE'
        assert isinstance(row['body'],str) and row['body'],'MISSING_BODY_RECORD'
    violations=[r for r in rows if (r['kind']=='axiom' and r['actual_name'] not in ALLOWED) or not set(r['axiom_references'])<=ALLOWED]
    assert bool(violations)==expect_reject,'WRONG_EXPECTED_AXIOM_RESULT'
    assert bool(data['rejects'])==expect_reject,'REJECT_RECORD'
    return rows
