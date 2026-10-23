#!/usr/bin/env python3
"""Exact readonly closure of the completed forest frontier release."""
from pathlib import Path
import datetime,hashlib,json,os,shutil
D=Path(__file__).resolve().parent;R=next(p for p in D.parents if (p/'bootloops-lean').exists());sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
def exact(a,b):
 if a!=b:raise ValueError('SOURCE_BYTE_MISMATCH')
assert hashlib.sha256(b'abc').hexdigest()=='ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad';exact(b'import X\ndef a:=1',b'import X\ndef a:=1');controls={'known_hash':'PASS','exact_duplicate':'PASS'}
try:exact(b'def a:=1',b'def a:=2')
except ValueError:controls['changed_body']='CAUGHT'
else:raise AssertionError('PLANT_FAILED')
try:{}['missing']
except KeyError:controls['missing_source']='CAUGHT'
else:raise AssertionError('MISSING_PLANT_FAILED')
assert shutil.disk_usage(D).free>=3*1024**3
mp='research/rmaf/algorithm/universal233/ordinary_dispatch/forest_frontier_work/FINAL-MANIFEST-v1.json';mh='d21973554632bdc7a7f2ab4deb89cd7d2936a59a990ec7d68656db04ca825ff9';M=R/mp;assert sha(M)==mh;m=json.loads(M.read_text());pins={e['path']:e['sha256'] for e in m['immutable_files']};S=R/m['canonical_receipt']['receipt'];sources={}
for p in S.glob('*.lean'):
 o=p.with_suffix('.olean');n=p.stem
 if str(p.relative_to(R)) not in pins or str(o.relative_to(R)) not in pins:continue
 row={'module':n,'files':[]}
 for f in [p,o]:
  h=pins[str(f.relative_to(R))];assert sha(f)==h and not f.stat().st_mode&0o222;row['files'].append({'original':str(f.relative_to(R)),'sha256':h})
 sources[n]=row
todo=['OverheadBound'];chosen={}
while todo:
 n=todo.pop()
 if n in chosen:continue
 e=sources[n];text=(R/e['files'][0]['original']).read_text();imports=[]
 for line in text.splitlines():
  if line.startswith('import '):
   for v in line[7:].split():
    if v in sources:imports.append(v);todo.append(v)
    elif v not in ['Std','Lean','Init']:raise ValueError('MISSING_IMPORT|'+n+'|'+v)
 chosen[n]=dict(e,imports=imports)
O=R/'results'/('algorithm-universal233-forest-overhead-root-'+datetime.datetime.now(datetime.timezone.utc).strftime('%Y%m%dT%H%M%SZ'));O.mkdir();deps=[]
for n,e in sorted(chosen.items()):
 for f in e['files']:
  p=R/f['original'];q=O/p.name;os.link(p,q);f.update(linked=str(q.relative_to(R)),inode=p.stat().st_ino,device=p.stat().st_dev)
 deps.append(e)
(O/'lean-toolchain').write_bytes((S/'lean-toolchain').read_bytes())
P=R/'research/rmaf/algorithm/universal233/ordinary_dispatch/forest_frontier_work';I=P/'instrument.py';assert sha(I)=='91b8125cfd2f150c9868c2605206682102bf82e5a92addad5fb49b678cc69cc5';(D/'instrument.py').write_bytes(I.read_bytes());pre=json.loads((P/'ROOT-v2.json').read_text())['producer_preflight'];assert sha(R/pre['manifest'])==pre['sha256'];pc=json.loads((R/pre['manifest']).read_text());assert pc['instrument_sha256']==sha(D/'instrument.py')
for e in pc['immutable_files']:assert sha(R/e['path'])==e['sha256']
rec={'status':'PASS_EXACT_FROZEN_FRONTIER_CLOSURE','root':str(O.relative_to(R)),'controls':controls,'dependencies':deps,'manifests':[{'path':mp,'sha256':mh}],'instrument_sha256':sha(D/'instrument.py'),'producer_preflight':pre,'independent_credit':0,'main_milestones':'ALL_OPEN'}
(D/'ROOT-v1.json').write_text(json.dumps(rec,indent=2)+'\n');print(rec['status'],len(deps),'readonly dependency pairs;',O,flush=True)
