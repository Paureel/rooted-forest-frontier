#!/usr/bin/env python3
"""Exact immutable dependency union/closure; no source or olean is rebuilt."""
from pathlib import Path
import datetime,hashlib,json,os,shutil
D=Path(__file__).resolve().parent;R=next(p for p in D.parents if (p/'bootloops-lean').exists());sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
def exact(a,b):
 if a!=b:raise ValueError('SOURCE_BYTE_MISMATCH')
assert hashlib.sha256(b'abc').hexdigest()=='ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad';exact(b'fixed',b'fixed');controls={'known_hash':'PASS','exact_duplicate':'PASS'}
try:exact(b'def a := 1',b'def a := 2')
except ValueError:controls['changed_body']='CAUGHT'
else:raise AssertionError('PLANT_FAILED')
try:{}['missing']
except KeyError:controls['missing_source']='CAUGHT'
else:raise AssertionError('MISSING_PLANT_FAILED')
assert shutil.disk_usage(D).free>=3*1024**3
specs=[('research/rmaf/algorithm/universal233/ordinary_dispatch/fast_source_pool/release_v1/FAST-SOURCE-POOL-MANIFEST-v1.json','efa132be64d489544e2aeeffaa0d08494cb9986d28104024f200f1080e2fbb60','results/algorithm-universal233-fast-source-pool-20261015T194053203759Z',None),('research/rmaf/algorithm/universal233/ordinary_dispatch/hard2_overlap_selector/FINAL-MANIFEST-v1.json','1a60932e32c81eb480239f1e4d55b36567ea6be372d9b820bf9ad31b20fb2d4f','results/algorithm-universal233-ordinary-hard2-overlap-root-20261015T192812Z',['OverlapDefs','SourceGuards','Exhaustive','ActualHard2','PaidConsumers','PairGuards']),('research/rmaf/algorithm/universal233/ordinary_dispatch/both_bad_local_binding/FINAL-MANIFEST-v1.json','90a3ca2d369ed9f30822a1eb72bad4aea957e9013458ff3a43cb856b2eb964c4','results/algorithm-universal233-both-bad-local-root-20261015T195334Z',['CallbackLocality','OrdinaryLocal'])]
sources={};manifests=[]
for mp,h,root,names in specs:
 M=R/mp;assert sha(M)==h;m=json.loads(M.read_text());pins={e['path']:e['sha256'] for e in m['immutable_files']};S=R/root;manifests.append({'path':mp,'sha256':h})
 if names is None:names=[Path(p).stem for p in pins if Path(p).parent==Path(root) and Path(p).suffix=='.lean' and (S/(Path(p).stem+'.olean')).exists()]
 for n in names:
  row={'module':n,'files':[]}
  for ext in ['.lean','.olean']:
   p=S/(n+ext);ph=pins[str(p.relative_to(R))];assert sha(p)==ph and not p.stat().st_mode&0o222;row['files'].append({'original':str(p.relative_to(R)),'sha256':ph})
  if n in sources:exact((R/sources[n]['files'][0]['original']).read_bytes(),(S/(n+'.lean')).read_bytes())
  else:sources[n]=row
seeds=['PaidConsumers','PairGuards','OrdinaryLocal','GoodPair','MassAssembly','CallDecrease','Executable'];todo=list(seeds);chosen={}
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
O=R/'results'/('algorithm-universal233-hard2-paid-ordinary-root-'+datetime.datetime.now(datetime.timezone.utc).strftime('%Y%m%dT%H%M%SZ'));O.mkdir();deps=[]
for n,e in sorted(chosen.items()):
 for f in e['files']:
  p=R/f['original'];q=O/p.name;os.link(p,q);f.update(linked=str(q.relative_to(R)),inode=p.stat().st_ino,device=p.stat().st_dev)
 deps.append(e)
(O/'lean-toolchain').write_bytes((R/specs[0][2]/'lean-toolchain').read_bytes())
P=R/'research/rmaf/algorithm/universal233/rule5_common_selector_consumer';I=P/'instrument.py';assert sha(I)=='91b8125cfd2f150c9868c2605206682102bf82e5a92addad5fb49b678cc69cc5';(D/'instrument.py').write_bytes(I.read_bytes());pre=json.loads((P/'PRODUCER-PREFLIGHT-v1.json').read_text());assert sha(R/pre['manifest'])==pre['sha256'];pc=json.loads((R/pre['manifest']).read_text());assert pc['instrument_sha256']==sha(D/'instrument.py')
for e in pc['immutable_files']:assert sha(R/e['path'])==e['sha256']
rec={'status':'PASS_FROZEN_DEPENDENCY_HARDLINK_CLOSURE','root':str(O.relative_to(R)),'controls':controls,'seeds':seeds,'dependencies':deps,'manifests':manifests,'instrument_sha256':sha(D/'instrument.py'),'producer_preflight':pre,'independent_credit':0,'main_milestones':'ALL_OPEN'}
(D/'ROOT-v1.json').write_text(json.dumps(rec,indent=2)+'\n');print(rec['status'],len(deps),'readonly dependency pairs;',O,flush=True)
