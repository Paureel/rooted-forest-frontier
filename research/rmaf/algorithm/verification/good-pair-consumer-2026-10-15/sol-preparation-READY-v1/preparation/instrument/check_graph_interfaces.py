#!/usr/bin/env python3
"""One-shot fixed interface-control pass over prerelease plant receipts only."""
import importlib.util,json,hashlib
from fractions import Fraction as F
from pathlib import Path
p=Path(__file__).resolve().parent.parent
sp=importlib.util.spec_from_file_location('prep_graph',p/'instrument/prepare_graph_controls.py');m=importlib.util.module_from_spec(sp);sp.loader.exec_module(m)
data=json.loads((p/'fixtures-v1.json').read_text())
results=json.loads((p/'graph-pilot-v1.json').read_text())['fixtures']+json.loads((p/'graph-battery-v1.json').read_text())['fixtures']
checks=[]
def add(name,value):checks.append({'name':name,'pass':bool(value)})
for f,r in zip(data['fixtures'],results):
 t=m.x.Graph(f['T'])
 for cc in data['rational_c']:
  c=F(*cc);bound=c**-3+c**-4 if 'vertex'in f else c**-3
  add(f['id']+' same-list mass '+str(c),m.mass(r['calls'],c)<=bound)
 if 'vertex'in f:
  for call in r['calls']:
   parent=f['P'][0] if call['identity']=='clear-A' else f['P'][1]
   reg=[set(z['labels']) for z in m.regions(t,f['vertex'],set(parent))]
   for o in call['receipt']['outputs']:
    blocks=[b for b in o['partition'] if set(b)<=set(parent)]
    add(f['id']+' '+call['identity']+' actual vertex clearing',all(any(set(b)<=z for z in reg) and f['vertex'] not in t.hull(b) for b in blocks))
 else:
  add(f['id']+' actual edge nonempty mutual-clear sectors',r['edge_trace']['all_sectors_nonempty'] and r['edge_trace']['mutual_clear'])
vf=data['fixtures'][0];calls=m.calls_for(vf,3)
add('q3 first call retained and pruned',len(calls)==2 and calls[0]['identity']=='clear-A' and not calls[0]['receipt']['outputs'] and calls[0]['receipt']['pruned']>0 and calls[0]['receipt']['childAttempts']>0)
bad=results[-1];add('bad C is source-valid but not agreed',all(bad['source_valid_each']) and not any(bad['Q_agreement_each']))
out={'phase':'PRE-CANDIDATE ONLY','checks':checks,'denominator':len(checks),'passed':sum(z['pass'] for z in checks),'all_pass':all(z['pass'] for z in checks),'instrument_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),'candidate_contact':False,'candidate_compilation':False,'replication_increment':0}
(p/'graph-interface-results-v1.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps({k:v for k,v in out.items() if k!='checks'},indent=2))
raise SystemExit(0 if out['all_pass'] else 1)
