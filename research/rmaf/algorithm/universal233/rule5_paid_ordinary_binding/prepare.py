#!/usr/bin/env python3
"""Problem-specific immutable source/olean hard-link preparation; no rebuilds."""
from pathlib import Path
import datetime,hashlib,json,os,re,shutil
D=Path(__file__).resolve().parent;R=D.parents[4];B=D/'build';B.mkdir(exist_ok=True)
O=R/'results'/('algorithm-universal233-rule5-paid-ordinary-prepare-'+datetime.datetime.now(datetime.timezone.utc).strftime('%Y%m%dT%H%M%S%fZ'));O.mkdir()
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def pin(p,h):
 if sha(p)!=h:raise ValueError('SOURCE_OLEAN_PIN_MISMATCH|'+str(p))
p=O/'PinFixture.txt';p.write_text('abc');pin(p,'ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad');p.write_text('abd')
try:pin(p,'ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad')
except ValueError:control='CAUGHT'
else:raise AssertionError('CORRUPTION_SURVIVED')
assert shutil.disk_usage(O).free>=3*1024**3,'DISK_FLOOR_3GIB'
inputs=[('research/rmaf/algorithm/universal233/rule5_paid_selector_consumer/FINAL-MANIFEST-v1.json','5faadd8bf54ef7ce8a7ecc2b3f351595c43aec138eb0888828b26bddf357d7ad'),('research/rmaf/algorithm/universal233/ordinary_dispatch/forest_pretest01/FOREST-PRETEST01-MANIFEST-v1.json','6e79a07b451188ea43a8f380074bff22ee72cc5678ab861d7fdba065e7135602'),('research/rmaf/algorithm/universal233/ordinary_dispatch/resume_20261015T1810Z/local_ih_release_v1/LOCAL-IH-MANIFEST-v1.json','1b9e3debeb558e6ec8a8f526cd6e78668f66d4668bff6c9042739eb4e01d6fff')]
mods={};conflicts=[];receipts=[];frozen={}
for name,h in inputs:
 M=R/name;pin(M,h);m=json.loads(M.read_text())
 for e in m['immutable_files']:pin(R/e['path'],e['sha256']);frozen[str((R/e['path']).resolve())]=e['sha256']
 canonical=R/m.get('canonical_source_replay',m.get('canonical_receipt',''))
 for p in canonical.glob('*.lean'):
  if p.stem in mods and sha(p)!=sha(mods[p.stem]):conflicts.append(p.stem)
  else:mods[p.stem]=p
 receipts.append(dict(path=name,sha256=h,immutable_files_verified=len(m['immutable_files']),canonical=str(canonical.relative_to(R))))
seen=set();entries=[]
def visit(n):
 if n in seen:return
 seen.add(n);assert n not in conflicts,('IMPORT_COLLISION',n)
 p=mods[n];s=p.read_text()
 for dep in re.findall(r'^import\s+(\w+)\s*$',s,re.M):
  if dep not in ['Std','Lean']:visit(dep)
 pin(p,frozen[str(p.resolve())]);op=p.with_suffix('.olean');pin(op,frozen[str(op.resolve())])
 for source in [p,op]:
  dest=B/source.name
  if dest.exists():assert os.path.samefile(dest,source),'REFUSE_MUTATE_EXISTING_LINK'
  else:os.link(source,dest)
 entries.append(dict(module=n,source=str(p.relative_to(R)),source_sha256=sha(p),olean=str(op.relative_to(R)),olean_sha256=sha(op)))
for n in ['PaidRequests','SelectorControls','ForestPretestSemantics','ForestPretestControls','LocalExact']:visit(n)
(B/'lean-toolchain').write_bytes((R/'results/algorithm-universal233-rule5-paid-selector-replay-20261015T190139870140Z/lean-toolchain').read_bytes())
rec=dict(status='PASS_IMMUTABLE_HARD_LINK_INPUTS',controls=dict(clean='PASS',corrupted=control),dependencies=entries,manifests=receipts,ignored_nonclosure_collisions=conflicts,free_bytes=shutil.disk_usage(O).free)
(O/'certificate.json').write_text(json.dumps(rec,indent=2)+'\n');(D/'DEPENDENCIES.json').write_text(json.dumps(entries,indent=2)+'\n');(D/'INPUT-RECEIPT-v1.json').write_text(json.dumps(dict(receipt=str(O.relative_to(R)),sha256=sha(O/'certificate.json')),indent=2)+'\n')
print('PASS_IMMUTABLE_HARD_LINK_INPUTS',len(entries),O)
