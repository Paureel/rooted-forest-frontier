#!/usr/bin/env python3
"""Explicit adapter from own precontact stored-producer scanner to exact module set."""
import hashlib,json,pathlib
HERE=pathlib.Path(__file__).resolve().parent
mods=json.loads((HERE/'SOURCE-MAP-v1.json').read_text())['topological_order']
original=(HERE.parent/'toys/ProducerAudit.lean').read_text()
text=original.replace('private def knd', 'private def scientificNames : Array String := #['+','.join(json.dumps(n) for n in mods)+']\n\nprivate def knd',1)
text=text.replace('producer.toString.startsWith "Toy"','scientificNames.contains producer.toString')
text=text.replace('origin.toString.startsWith "Toy"','scientificNames.contains origin.toString')
text=text.replace('audit_producers!','audit_scientific!').replace('PRODUCER_TOY','SCIENTIFIC_PRODUCERS')
text=text.replace('if knd c == "axiom" && !standard.contains n then','if knd c == "axiom" then')
text=text.replace('("stored_count", toJson d.constants.size),','("stored_count", toJson d.constants.size),\n        ("olean_path", .str (← liftIO (findOLean producer)).toString),')
text=text.replace('let out := Json.mkObj [','for mod in mods do\n    let s := mod.toString\n    unless scientificNames.contains s || s == "ScientificAudit" || s == "Init" || s.startsWith "Init." || s == "Std" || s.startsWith "Std." || s == "Lean" || s.startsWith "Lean." do\n      rejected := rejected.push s!"unexpected-nonstandard-module:{s}"\n  let out := Json.mkObj [\n    ("all_modules", ss (mods.map Name.toString)),')
(HERE/'build/ScientificAudit.lean').write_text(text)
for name,selected in [('AuditPilot',mods[:5]),('AuditScientific',mods)]:
    output=HERE/(name+'.json')
    source='import ScientificAudit\n'+''.join('import '+m+'\n' for m in selected)
    source+='audit_scientific! "'+str(output)+'"\n'
    (HERE/'build'/(name+'.lean')).write_text(source)
record={'own_precontact_scanner_sha256':hashlib.sha256(original.encode()).hexdigest(),
    'changes':['Toy-prefix→exact160 source-module whitelist','inventory actual scientific olean paths',
      'reject any scientific direct axiom including standard-named shadow','reject unknown nonstandard imports',
      'rename audit command/label; full raw stored/resolved type/body/dependencies retained'],
    'generated_sha256':hashlib.sha256(text.encode()).hexdigest(),
    'modules':mods,'candidate_body_changes':False}
(HERE/'SCIENTIFIC-AUDIT-ADAPTER-v1.json').write_text(json.dumps(record,indent=2)+'\n')
print(json.dumps({'scanner_sha256':record['generated_sha256'],'scientific_modules':len(mods)}))
