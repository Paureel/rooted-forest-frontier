#!/usr/bin/env python3
"""One-shot exact import root for this caller extension, not a package union."""
from pathlib import Path
import datetime,hashlib,json,os,shutil
D=Path(__file__).resolve().parent;R=next(p for p in D.parents if (p/'bootloops-lean').exists());sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
T=R/'research/rmaf/monitoring/next-20261016T092054Z/BINARY-CALLER-TARGET-v1.json';assert sha(T)=='6f0d4bfbeeb5318b01674b729139821b4df671136859324572068e2af0600d99';t=json.loads(T.read_text());m=R/t['previous_completed']['manifest'];assert sha(m)==t['previous_completed']['sha256'];a=json.loads(m.read_text());F=R/a['canonical_receipt'];pins={x['path']:x['sha256'] for x in a['immutable_files']}
for name in ['ForestProgram','RMAF','ReturnedPayload']:
 p=F/(name+'.lean');assert sha(p)==pins[str(p.relative_to(R))]
 if name!='ReturnedPayload':
  q=R/'results/algorithm-universal233-fast-ordinary-recursion-replay-20261015T205325296780Z'/(name+'.lean');assert p.read_bytes()==q.read_bytes(),('SOURCE_POOL_COLLISION',name)
assert shutil.disk_usage(D).free>=3*1024**3
O=R/'results'/('algorithm-universal233-binary-caller-root-20261016T092054Z-'+datetime.datetime.now(datetime.timezone.utc).strftime('%Y%m%dT%H%M%SZ'));O.mkdir();deps=[]
for p in sorted(F.glob('*.olean')):
 s=p.with_suffix('.lean')
 if not s.exists() or p.stem=='ProviderAuditGhost':continue
 if str(s.relative_to(R)) not in pins or str(p.relative_to(R)) not in pins:continue
 files=[]
 for f in [s,p]:
  assert sha(f)==pins[str(f.relative_to(R))];q=O/f.name;assert not f.stat().st_mode&0o222;os.link(f,q)
  files.append({'original':str(f.relative_to(R)),'linked':str(q.relative_to(R)),'sha256':sha(f),'original_mode':oct(f.stat().st_mode&0o777),'original_inode':f.stat().st_ino})
 deps.append({'module':p.stem,'files':files})
assert len(deps)==489,len(deps)
(O/'lean-toolchain').write_text('leanprover/lean4:v4.35.0\n')
old=R/'research/rmaf/algorithm/universal233/ordinary_dispatch/forest_binary_provider_binding'
for n in ['pilot.py','instrument.py']:(D/n).write_bytes((old/n).read_bytes())
rec={'root':str(O.relative_to(R)),'dependencies':deps,'pin':str(T.relative_to(R)),'pin_sha256':sha(T),'licensed_persistent_manifest':str(m.relative_to(R)),'licensed_persistent_sha256':sha(m),'source_pool':'Only the exact completed persistent checker pool; ForestProgram/RMAF source bytes independently matched the licensed functional root. Other licensed packages not merged.','dependency_rebuilds':0,'independent_credit':0}
(D/'ROOT-v1.json').write_text(json.dumps(rec,indent=2)+'\n');print('EXACT_ROOT',len(deps),'pairs',O,flush=True)
