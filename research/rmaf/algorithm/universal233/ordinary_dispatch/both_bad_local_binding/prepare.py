#!/usr/bin/env python3
"""Snapshot only a pinned completed source closure; never alter pool files."""
from pathlib import Path
import datetime,hashlib,json,re,shutil
D=Path(__file__).resolve().parent;R=next(p for p in D.parents if (p/'bootloops-lean').exists());sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
P=R/'results/algorithm-universal233-fast-source-pool-20261015T194053203759Z';C=P/'certificate.json';raw=C.read_bytes();cert=json.loads(raw)
def adapt(s,m):
 return re.sub(r'(?m)^(import\s+)([^\r\n]+)$',lambda z:z[1]+re.sub(r'[A-Za-z_][A-Za-z0-9_.]*',lambda n:m.get(n[0],n[0]),z[2]),s)
def equal(a,b):
 if a!=b:raise ValueError('SOURCE_BYTE_MISMATCH')
assert hashlib.sha256(b'abc').hexdigest()=='ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad'
equal(adapt('import A\ndef n := 3\n',{'A':'B'}),'import B\ndef n := 3\n');controls={'known_hash':'PASS','exact_import_adaptation':'PASS'}
for tag,a,b in [('changed_body','import B\ndef n := 3\n','import B\ndef n := 4\n'),('wrong_import','import B\ndef n := 3\n',adapt('import A\ndef n := 3\n',{'A':'C'}))]:
 try:equal(a,b)
 except ValueError:controls[tag]='CAUGHT'
 else:raise AssertionError(tag)
assert shutil.disk_usage(D).free>=3*1024**3
catalog={};manifests=[]
for name,h in cert['inputs'].items():
 if 'MANIFEST' not in Path(name).name:continue
 p=R/name;assert sha(p)==h;x=json.loads(p.read_text());manifests.append({'path':name,'sha256':h})
 for e in x.get('immutable_files',[]):catalog[e['path']]=e['sha256']
extra=R/'research/rmaf/algorithm/universal233/ordinary_dispatch/resume_20261015T1810Z/local_ih_release_v1/LOCAL-IH-MANIFEST-v1.json';assert sha(extra)=='1b9e3debeb558e6ec8a8f526cd6e78668f66d4668bff6c9042739eb4e01d6fff';manifests.append({'path':str(extra.relative_to(R)),'sha256':sha(extra)})
for e in json.loads(extra.read_text())['immutable_files']:catalog[e['path']]=e['sha256']
entries={e['module']:e for e in cert['source_entries']};seeds=['Dispatcher','OrdinaryBridge','PlanCover','CallDecrease','LocalCongruence','ForestMinimumCompletion','DispatchControls','BothPrecontrols'];todo=list(seeds);chosen={}
while todo:
 n=todo.pop()
 if n in chosen:continue
 e=entries[n];p=P/(n+'.lean');assert sha(p)==e['sha256'];text=p.read_text();origin=None
 for a in e['origins']:
  if catalog.get(a['source'])!=a['source_sha256']:continue
  q=R/a['source'];assert sha(q)==a['source_sha256']
  if adapt(q.read_text(),a['import_adaptations'])==text:origin=a;break
 if origin is None:raise ValueError('NO_FROZEN_EXACT_ORIGIN|'+n)
 imports=[]
 for line in text.splitlines():
  if line.startswith('import '):
   for v in line[7:].split():
    if v in entries:imports.append(v);todo.append(v)
    elif v not in ['Std','Lean','Init']:raise ValueError('UNKNOWN_IMPORT|'+n+'|'+v)
 chosen[n]={'entry':e,'origin':origin,'imports':imports}
O=R/'results'/('algorithm-universal233-both-bad-local-root-'+datetime.datetime.now(datetime.timezone.utc).strftime('%Y%m%dT%H%M%SZ'));O.mkdir();(O/'parent-pool-certificate-snapshot.json').write_bytes(raw);deps=[]
for n,v in sorted(chosen.items()):
 row={'module':n,'frozen_origin':v['origin'],'imports':v['imports'],'files':[]}
 for suffix in ['.lean','.olean']:
  p=P/(n+suffix);h=sha(p);q=O/p.name;shutil.copyfile(p,q);assert sha(q)==h;q.chmod(0o444);row['files'].append({'pool_source':str(p.relative_to(R)),'copied':str(q.relative_to(R)),'sha256':h})
 deps.append(row)
(O/'lean-toolchain').write_bytes((P/'lean-toolchain').read_bytes())
I=R/'research/rmaf/algorithm/universal233/rule5_common_selector_consumer/instrument.py';assert sha(I)=='91b8125cfd2f150c9868c2605206682102bf82e5a92addad5fb49b678cc69cc5';(D/'instrument.py').write_bytes(I.read_bytes())
pre=json.loads((I.parent/'PRODUCER-PREFLIGHT-v1.json').read_text());assert sha(R/pre['manifest'])==pre['sha256'];pm=json.loads((R/pre['manifest']).read_text());assert pm['instrument_sha256']==sha(D/'instrument.py')
for e in pm['immutable_files']:assert sha(R/e['path'])==e['sha256']
plan=R/'research/rmaf/algorithm/universal233/ordinary_dispatch/fast_dispatch/FAST-DISPATCH-PLAN-v1.md';(D/'FAST-DISPATCH-PLAN-SNAPSHOT-v1.md').write_bytes(plan.read_bytes())
overlap=R/'research/rmaf/algorithm/universal233/ordinary_dispatch/hard2_overlap_selector/FINAL-MANIFEST-v1.json';assert sha(overlap)=='1a60932e32c81eb480239f1e4d55b36567ea6be372d9b820bf9ad31b20fb2d4f'
rec={'status':'PASS_FROZEN_ORIGIN_CLOSURE_SNAPSHOT','root':str(O.relative_to(R)),'controls':controls,'seeds':seeds,'dependencies':deps,'frozen_manifests':manifests,'parent_pool_certificate_snapshot_sha256':hashlib.sha256(raw).hexdigest(),'parent_pool_status_at_snapshot':cert['status'],'parent_pool_olean_scope':'Compiled selected source-bound bytes copied/pinned as DEVELOPMENT dependencies; no fresh imported-pool rebuild or producer acceptance.','producer_preflight':pre,'instrument_sha256':sha(D/'instrument.py'),'plan':{'source':str(plan.relative_to(R)),'sha256':sha(plan)},'overlap_manifest':{'path':str(overlap.relative_to(R)),'sha256':sha(overlap)},'independent_credit':0,'main_milestones':'ALL_OPEN'}
(D/'ROOT-v1.json').write_text(json.dumps(rec,indent=2)+'\n');print(rec['status'],len(deps),'readonly dependency pairs;',O,flush=True)
