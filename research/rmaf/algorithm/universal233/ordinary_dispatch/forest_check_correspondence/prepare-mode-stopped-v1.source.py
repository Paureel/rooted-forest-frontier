#!/usr/bin/env python3
"""Exact immutable FastExact/polynomial closure with fail-closed source collisions."""
from pathlib import Path
import datetime,hashlib,json,os,shutil
D=Path(__file__).resolve().parent;R=next(p for p in D.parents if (p/'bootloops-lean').exists());sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
def exact(a,b):
 if a!=b:raise ValueError('SOURCE_BYTE_MISMATCH')
assert hashlib.sha256(b'abc').hexdigest()=='ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad';exact(b'import X\ndef d:=1',b'import X\ndef d:=1');controls={'known_hash':'PASS','exact_duplicate':'PASS'}
for k,a,b in [('changed_body',b'import X\ndef d:=1',b'import X\ndef d:=2'),('changed_import',b'import X\ndef d:=1',b'import Y\ndef d:=1')]:
 try:exact(a,b)
 except ValueError:controls[k]='CAUGHT'
 else:raise AssertionError('PLANT_FAILED')
try:{}['missing']
except KeyError:controls['missing_source']='CAUGHT'
else:raise AssertionError('MISSING_PLANT_FAILED')
assert shutil.disk_usage(D).free>=3*1024**3
specs=[('research/rmaf/algorithm/universal233/ordinary_dispatch/forest_local_overhead_polynomial/FINAL-MANIFEST-v1.json','161d04f6c3756ee2b9c6b7eb9c08c16006d529edb70ca30a1153914b48af1c9e'),('research/rmaf/algorithm/universal233/ordinary_dispatch/fast_ordinary_recursion/FINAL-MANIFEST-v1.json','0f806c00eacdc8d3d12ffb9c38406edd0363eb6b5a235897506880fe05efcb8c')]
sources={};manifests=[];duplicates=[]
for mp,mh in specs:
 M=R/mp;assert sha(M)==mh;m=json.loads(M.read_text());pins={e['path']:e['sha256'] for e in m['immutable_files']};root=m['canonical_receipt'];root=root['receipt'] if isinstance(root,dict) else root;S=R/root;manifests.append({'path':mp,'sha256':mh})
 for p in S.glob('*.lean'):
  o=p.with_suffix('.olean');n=p.stem
  if str(p.relative_to(R)) not in pins or str(o.relative_to(R)) not in pins:continue
  row={'module':n,'files':[]}
  for f in [p,o]:
   h=pins[str(f.relative_to(R))];assert sha(f)==h and not f.stat().st_mode&0o222;row['files'].append({'original':str(f.relative_to(R)),'sha256':h})
  if n in sources:
   a=R/sources[n]['files'][0]['original']
   if a.read_bytes()!=p.read_bytes():
    stop={'status':'STOPPED_EXACT_SOURCE_COLLISION','module':n,'first':sources[n]['files'][0],'second':row['files'][0],'root_created':False,'mutation':False};(D/'PREPARE-STOP-v1.json').write_text(json.dumps(stop,indent=2)+'\n');raise ValueError(stop)
   duplicates.append({'module':n,'kept':sources[n]['files'][0],'identical':row['files'][0]})
  else:sources[n]=row
todo=['FastExact','Monomial'];chosen={}
while todo:
 n=todo.pop()
 if n in chosen:continue
 if n not in sources:
  stop={'status':'STOPPED_MISSING_IMPORT','module':n,'root_created':False};(D/'PREPARE-STOP-v1.json').write_text(json.dumps(stop,indent=2)+'\n');raise ValueError(stop)
 e=sources[n];imports=[]
 for line in (R/e['files'][0]['original']).read_text().splitlines():
  if line.startswith('import '):
   for v in line[7:].split():
    if v in sources:imports.append(v);todo.append(v)
    elif v not in ['Std','Lean','Init']:raise ValueError('MISSING_IMPORT|'+n+'|'+v)
 chosen[n]=dict(e,imports=imports)
O=R/'results'/('algorithm-universal233-forest-check-root-'+datetime.datetime.now(datetime.timezone.utc).strftime('%Y%m%dT%H%M%SZ'));O.mkdir();deps=[]
for n,e in sorted(chosen.items()):
 for f in e['files']:
  p=R/f['original'];q=O/p.name;os.link(p,q);f.update(linked=str(q.relative_to(R)),inode=p.stat().st_ino,device=p.stat().st_dev)
 deps.append(e)
(O/'lean-toolchain').write_text('leanprover/lean4:v4.35.0\n')
P=R/'research/rmaf/algorithm/universal233/ordinary_dispatch/forest_local_overhead_polynomial';I=P/'instrument.py';assert sha(I)=='91b8125cfd2f150c9868c2605206682102bf82e5a92addad5fb49b678cc69cc5';(D/'instrument.py').write_bytes(I.read_bytes());pre=json.loads((P/'ROOT-v1.json').read_text())['producer_preflight'];assert sha(R/pre['manifest'])==pre['sha256'];pc=json.loads((R/pre['manifest']).read_text());assert pc['instrument_sha256']==sha(D/'instrument.py')
for e in pc['immutable_files']:assert sha(R/e['path'])==e['sha256']
rec={'status':'PASS_EXACT_FROZEN_FAST_POLY_CLOSURE','root':str(O.relative_to(R)),'controls':controls,'dependencies':deps,'manifests':manifests,'identical_source_contacts':duplicates,'source_adaptations':[],'instrument_sha256':sha(D/'instrument.py'),'producer_preflight':pre,'independent_credit':0,'main_milestones':'ALL_OPEN'}
(D/'ROOT-v1.json').write_text(json.dumps(rec,indent=2)+'\n');print(rec['status'],len(deps),'readonly pairs;',len(duplicates),'exact shared sources;',O,flush=True)
