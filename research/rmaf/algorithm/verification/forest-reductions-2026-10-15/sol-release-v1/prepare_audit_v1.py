#!/usr/bin/env python3
"""One-shot exact source-origin adapter of the frozen, planted-tested reviewer audit."""
import json,pathlib
HERE=pathlib.Path(__file__).resolve().parent; B=HERE/'isolated'; mods=[r['module'] for r in json.loads((HERE/'release-integrity-v1.json').read_text())['formalModules']]
header='import Lean\nopen Lean Elab Command\n\ndef solSourceModules : List String := '+repr(mods).replace("'",'"')+'\n'
body=r'''
private def solOrigin (env : Environment) (n : Name) : String :=
  match env.getModuleIdxFor? n with
  | some i => toString env.header.moduleNames[i.toNat]!
  | none => toString env.mainModule

private def solInheritedOrigin (env : Environment) (n : Name) : Option (String × String) := Id.run do
  let mut p := n.getPrefix
  for _ in [:n.getNumParts] do
    if p.isAnonymous then return none
    if let some i := env.getModuleIdxFor? p then
      let origin := toString env.header.moduleNames[i.toNat]!
      if solSourceModules.contains origin then return some (origin, toString p)
    p := p.getPrefix
  return none

elab "#sol_force_all" : command => do
  let env ← getEnv
  let producers := env.constants.toList.filterMap fun (n, ci) =>
    if solSourceModules.contains (solOrigin env n) then
      match ci with
      | .defnInfo _ => some n
      | _ => none
    else none
  let env' ← liftTermElabM fun _ => do
    for n in producers do
      let _ ← Meta.getEqnsFor? n
    getEnv
  setEnv env'
  liftIO <| IO.println s!"FORCED\t{producers.length}"

elab "#sol_candidate_inventory " tag:str : command => do
  let env ← getEnv
  for mod in env.header.moduleNames do
    let s := toString mod
    if solSourceModules.contains s then
      let path ← liftIO <| findOLean mod
      let real ← liftIO <| IO.FS.realPath path
      liftIO <| IO.println <| "MODULE\t" ++ tag.getString ++ "\t" ++ s ++ "\t" ++ real.toString
    else if !(s == "Init" || s.startsWith "Init." || s == "Std" || s.startsWith "Std." || s == "Lean" || s.startsWith "Lean." || s == "SolAudit") then
      throwError "unmapped imported module {mod}"
  let locals ← liftIO <| env.getLocalConstantInfos
  let mut rows := env.constants.toList
  for c in locals do
    if !rows.any (fun r => r.1 == c.name) then rows := (c.name,c.constInfo.get) :: rows
  for (n, ci) in rows do
    let raw := solOrigin env n
    let (origin, adapter) := if (env.getModuleIdxFor? n).isNone then
      match solInheritedOrigin env n with
      | some (m,p) => (m,"generated-prefix:" ++ p)
      | none => (raw,"direct")
      else (raw,"direct")
    if solSourceModules.contains origin then
      let kind := match ci with
        | .axiomInfo _ => "axiom"
        | .thmInfo _ => "theorem"
        | .defnInfo _ => "definition"
        | .opaqueInfo _ => "opaque"
        | .quotInfo _ => "quot"
        | .inductInfo _ => "inductive"
        | .ctorInfo _ => "constructor"
        | .recInfo _ => "recursor"
      let axs ← liftCoreM <| collectAxioms n
      liftIO <| IO.println <| "ROW\t" ++ tag.getString ++ "\t" ++ toString n ++ "\t" ++ origin ++ "\t" ++ kind ++ "\t" ++ String.intercalate "," (axs.toList.map toString) ++ "\t" ++ raw ++ "\t" ++ adapter
      if kind == "theorem" then
        let ty ← liftTermElabM fun _ => Meta.ppExpr ci.type
        liftIO <| IO.println <| "TYPE\t" ++ tag.getString ++ "\t" ++ toString n ++ "\t" ++ (Json.str ty.pretty).compress
'''
(B/'SolAudit.lean').write_text(header+body)
for name,commands in [('ProbeAuditPilot','#sol_candidate_inventory "pilot"\n'),('ProbeAuditFull','#sol_candidate_inventory "before"\n#sol_force_all\n#sol_candidate_inventory "after"\n')]:
 (B/(name+'.lean')).write_text('import SolAudit\nimport CompletionConsumers\nimport Consumers\n'+commands)
(HERE/'AUDIT-ADAPTER-v1.json').write_text(json.dumps({'sourceModules':mods,'standardOrigins':['Init','Init.*','Std','Std.*','Lean','Lean.*'],'reviewerModules':['SolAudit','ProbeAuditPilot','ProbeAuditFull'],'sourceValuesChanged':False,'frozenComparatorBase':'sol-frozen-ready-v1/preparation/audit_controls_v5.py','generatedOrigin':'keep raw probe origin; attribute only to longest existing imported source-declaration prefix and validate the exact producer pair against pre-force inventory'},indent=2)+'\n')
