#!/usr/bin/env python3
"""Versioned producer selection correction; source literal defs/abbrevs only."""
import json,pathlib,re
H=pathlib.Path(__file__).resolve().parent;B=H/'isolated'; baseline=json.loads((H/'audit-pilot-v1.json').read_text())['pilot']['rows'];mods=json.loads((H/'release-integrity-v1.json').read_text())['formalModules'];producers=[]
for m in mods:
 for lineno,line in enumerate((B/(m['module']+'.lean')).read_text().splitlines(),1):
  match=re.match(r'^(?:(?:private|protected|noncomputable|partial|unsafe)\s+)*(?:def|abbrev)\s+([\w.]+)',line)
  if not match:continue
  stem=match[1]; matches=[r for r in baseline if r['origin']==m['module'] and r['kind']=='definition' and (r['name']==stem or r['name'].endswith('.'+stem))]
  assert len(matches)==1,(m['module'],lineno,line,matches)
  producers.append({'name':matches[0]['name'],'origin':m['module'],'line':lineno,'literal':line})
assert len({r['name'] for r in producers})==len(producers)
(H/'SOURCE-PRODUCERS-v2.json').write_text(json.dumps({'method':'unique actual baseline definition name/origin match for every literal def/abbrev source line; no silent skip','producers':producers,'count':len(producers),'notRegenerated':'compiler-generated internal private match/splitter/unsafe implementation definitions remain fully inventoried but are not reinterpreted as source definition producers'},indent=2)+'\n')
s=(B/'SolAudit.lean').read_text();start=s.index('  let producers :=');end=s.index('  let env\' ←',start)
s=s[:start]+'  let producers : List Name := ['+', '.join('`'+r['name'] for r in producers)+']\n'+s[end:];s=s.replace('s == "SolAudit"','s == "SolAuditV2"');(B/'SolAuditV2.lean').write_text(s)
for name,commands in [('ProbeAuditPilotV2','#sol_candidate_inventory "pilot"\n'),('ProbeAuditFullV2','#sol_candidate_inventory "before"\n#sol_force_all\n#sol_candidate_inventory "after"\n')]:
 (B/(name+'.lean')).write_text('import SolAuditV2\nimport CompletionConsumers\nimport Consumers\n'+commands)
r=(H/'run_audit_v1.py').read_text().replace("logs=HERE/'audit-logs'", "logs=HERE/'audit-logs-v2'").replace('SolAudit.olean','SolAuditV2.olean').replace('SolAudit.lean','SolAuditV2.lean').replace('compile-SolAudit','compile-SolAuditV2').replace('ProbeAuditPilot.lean','ProbeAuditPilotV2.lean').replace('ProbeAuditFull.lean','ProbeAuditFullV2.lean').replace("'ProbeAuditFull'", "'ProbeAuditFullV2'").replace('audit-pilot-v1.json','audit-pilot-v2.json').replace('audit-full-v1.json','audit-full-v2.json')
r=r.replace('assert r.returncode==0,r.stdout', "assert r.returncode==0,{'failed':label,'exit':r.returncode,'see':str(logs/(label+'.log'))}")
(H/'run_audit_v2.py').write_text(r)
print(json.dumps({'literalSourceProducers':len(producers)}))
