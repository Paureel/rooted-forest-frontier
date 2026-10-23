#!/usr/bin/env python3
"""Problem-specific manifest-bound combined completed source preparation."""
from pathlib import Path
import datetime,hashlib,json,re,shutil
D=Path(__file__).resolve().parent;R=D.parents[4]
O=R/'results'/('algorithm-universal233-rule5-paid-selector-prepare-'+datetime.datetime.now(datetime.timezone.utc).strftime('%Y%m%dT%H%M%S%fZ'));O.mkdir()
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def pin(p,h):
 if sha(p)!=h:raise ValueError('SOURCE_PIN_MISMATCH|'+str(p))
# Planted clean and one-byte hostile twins precede actual source audit.
fixture=O/'PinFixture.txt';fixture.write_text('abc');pin(fixture,'ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad')
fixture.write_text('abd')
try:pin(fixture,'ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad')
except ValueError:control='CAUGHT'
else:raise AssertionError('SOURCE_CORRUPTION_SURVIVED')
assert shutil.disk_usage(O).free>=3*1024**3,'DISK_FLOOR_3GIB'
ms=[('research/rmaf/algorithm/universal233/rule5_case322_paid_guard/RULE5-CASE322-PAID-GUARD-MANIFEST-v1.json','a1c3805010404da55836b2762b732c48c96132b4038edd074ac3da384a4bc0c1'),('research/rmaf/algorithm/universal233/rule5_source_orientation_consumer/FINAL-MANIFEST-v1.json','a27469192042dff5e1001961ed64bac312b3c0f527ba02056263bda19a3b5fd8')]
canon=[];receipts=[]
for name,h in ms:
 p=R/name;pin(p,h);m=json.loads(p.read_text())
 for e in m['immutable_files']:pin(R/e['path'],e['sha256'])
 q=m['canonical_receipt'];c=R/q['receipt'];canon.append(c);receipts.append(dict(manifest=name,sha256=h,immutable_files_verified=len(m['immutable_files']),canonical=str(c.relative_to(R))))
mods={};conflicts=[]
for c in canon:
 for p in c.glob('*.lean'):
  n=p.stem
  if n in mods and sha(p)!=sha(mods[n]):conflicts.append(dict(module=n,paths=[str(mods[n].relative_to(R)),str(p.relative_to(R))]))
  else:mods[n]=p
# Only the transitive scientific source closure is admitted; controls/auditors
# with common names outside it are not imported or adapted.
order=[];seen=set();entries=[]
def visit(n):
 if n in seen:return
 seen.add(n)
 assert not any(e['module']==n for e in conflicts),('IMPORT_COLLISION',n)
 p=mods[n];s=p.read_text()
 for dep in re.findall(r'^import\s+(\w+)\s*$',s,re.M):
  if dep not in ['Std','Lean']:visit(dep)
 order.append(n);entries.append(dict(module=n,path=str(p.relative_to(R)),sha256=sha(p),adapted_sha256=sha(p),adaptations={}))
visit('PaidCaller');visit('FinalInterface')
B=D/'build';B.mkdir(exist_ok=True)
for e in entries:
 p=R/e['path'];(B/(e['module']+'.lean')).write_bytes(p.read_bytes())
 old=p.with_suffix('.olean');assert old.exists(),old;(B/old.name).write_bytes(old.read_bytes())
(B/'lean-toolchain').write_bytes((canon[0]/'lean-toolchain').read_bytes())
rec=dict(status='PASS_INPUT_SOURCE_BINDING',source_pin_control=control,manifests=receipts,scientific_modules=len(entries),ignored_nonclosure_name_collisions=conflicts,entries=entries,free_bytes=shutil.disk_usage(O).free)
(O/'certificate.json').write_text(json.dumps(rec,indent=2)+'\n');(D/'INPUT-RECEIPT-v1.json').write_text(json.dumps(dict(receipt=str(O.relative_to(R)),sha256=sha(O/'certificate.json')),indent=2)+'\n');(D/'STACK-PINS.json').write_text(json.dumps(entries,indent=2)+'\n')
print('PASS_INPUT_SOURCE_BINDING',len(entries),O)
