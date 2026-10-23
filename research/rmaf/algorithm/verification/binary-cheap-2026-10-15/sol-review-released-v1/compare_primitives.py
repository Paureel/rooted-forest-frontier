#!/usr/bin/env python3
"""Actual compiled clean/false controls against frozen READY primitive values."""
from pathlib import Path
import hashlib,json
P=Path(__file__).resolve().parent;R=P.parent/'sol-preparation-READY-v1/preparation'
data=json.loads((R/'fixtures-v1.json').read_text());log=P/'logs/pilot-ReadoutPrimitives.log';rows=[json.loads(z[len('READOUT_JSON '):])for z in log.read_text().splitlines()if z.startswith('READOUT_JSON ')];checks=[]
def add(n,g,w):checks.append({'name':n,'got':g,'expected':w,'pass':g==w})
add('topology same',rows[0]['same'],True);add('topology deliberately false',rows[0]['wrong'],False)
can=lambda p:sorted(sorted(b)for b in p)
for r in rows[1:]:
 e=data['primitive_controls'][r['primitive']];v=r['receipt']
 if 'expected_costs'in e:add(r['primitive']+' costs',[len(o['sourceCuts'])for o in v['outputs']],e['expected_costs'])
 if 'expected_parts'in e:add(r['primitive']+' parts',sorted(can(o['partition'])for o in v['outputs']),sorted(can(o)for o in e['expected_parts']))
 if 'expected_refusal'in e:add(r['primitive']+' exact refusal',v['refusals'],[e['expected_refusal']])
out={'checks':checks,'denominator':len(checks),'passed':sum(z['pass']for z in checks),'all_pass':all(z['pass']for z in checks),'log_sha256':hashlib.sha256(log.read_bytes()).hexdigest(),'fixture_sha256':hashlib.sha256((R/'fixtures-v1.json').read_bytes()).hexdigest()};(P/'compiled-primitive-comparison-v1.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps({k:v for k,v in out.items()if k!='checks'},indent=2));assert out['all_pass']
