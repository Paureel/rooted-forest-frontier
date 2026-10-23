#!/usr/bin/env python3
"""Problem-specific immutable source/olean hard-link preparation; no rebuilds."""
from pathlib import Path
import datetime,hashlib,json,os,re,shutil
D=Path(__file__).resolve().parent;R=D.parents[5];B=D/'build';B.mkdir(exist_ok=True)
O=R/'results'/('algorithm-universal233-rule5-ordinary-dispatch-prepare-'+datetime.datetime.now(datetime.timezone.utc).strftime('%Y%m%dT%H%M%S%fZ'));O.mkdir()
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def pin(p,h):
 if sha(p)!=h:raise ValueError('SOURCE_OLEAN_PIN_MISMATCH|'+str(p))
p=O/'PinFixture.txt';p.write_text('abc');pin(p,'ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad');p.write_text('abd')
try:pin(p,'ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad')
except ValueError:control='CAUGHT'
else:raise AssertionError('CORRUPTION_SURVIVED')
assert shutil.disk_usage(O).free>=3*1024**3,'DISK_FLOOR_3GIB'
inputs=[('research/rmaf/algorithm/universal233/ordinary_dispatch/fast_source_pool/release_v1/FAST-SOURCE-POOL-MANIFEST-v1.json','efa132be64d489544e2aeeffaa0d08494cb9986d28104024f200f1080e2fbb60')]
mods={};conflicts=[];receipts=[];frozen={};canonicals=[]
for name,h in inputs:
 M=R/name;pin(M,h);m=json.loads(M.read_text())
 for e in m['immutable_files']:pin(R/e['path'],e['sha256']);frozen[str((R/e['path']).resolve())]=e['sha256']
 canonical=R/m.get('canonical_build',m.get('canonical_source_replay',m.get('canonical_receipt','')));canonical=canonical.parent if canonical.suffix=='.json' else canonical
 canonicals.append(canonical)
 receipts.append(dict(path=name,sha256=h,immutable_files_verified=len(m['immutable_files']),canonical=str(canonical.relative_to(R))))
seen={};entries=[]
def visit(n,canonical):
 p=canonical/(n+'.lean');assert p.exists(),('MISSING_SOURCE',n,str(canonical))
 if n in seen:
  assert sha(p)==sha(seen[n]),('GENUINE_CLOSURE_IMPORT_COLLISION',n,str(p),str(seen[n]))
  return
 seen[n]=p;s=p.read_text()
 for dep in re.findall(r'^import\s+(\w+)\s*$',s,re.M):
  if dep not in ['Std','Lean']:visit(dep,canonical)
 pin(p,frozen[str(p.resolve())]);op=p.with_suffix('.olean');pin(op,frozen[str(op.resolve())])
 for source in [p,op]:
  dest=B/source.name
  if dest.exists():assert sha(dest)==sha(source),'REFUSE_MUTATE_EXISTING_LINK'
  else:os.link(source,dest)
 entries.append(dict(module=n,source=str(p.relative_to(R)),source_sha256=sha(p),olean=str(op.relative_to(R)),olean_sha256=sha(op)))
for n,i in [('OrdinaryBinding',0),('SelectedExact',0),('RecursiveConsumers',0),('ChildForestBinding',0),('Rule5PreControls',0)]:visit(n,canonicals[i])
(B/'lean-toolchain').write_bytes((R/'results/algorithm-universal233-fast-source-pool-20261015T194053203759Z/lean-toolchain').read_bytes())
rec=dict(status='PASS_IMMUTABLE_HARD_LINK_INPUTS',controls=dict(clean='PASS',corrupted=control),dependencies=entries,manifests=receipts,ignored_nonclosure_collisions=conflicts,free_bytes=shutil.disk_usage(O).free)
(O/'certificate.json').write_text(json.dumps(rec,indent=2)+'\n');(D/'DEPENDENCIES.json').write_text(json.dumps(entries,indent=2)+'\n');(D/'INPUT-RECEIPT-v1.json').write_text(json.dumps(dict(receipt=str(O.relative_to(R)),sha256=sha(O/'certificate.json')),indent=2)+'\n')
print('PASS_IMMUTABLE_HARD_LINK_INPUTS',len(entries),O)
