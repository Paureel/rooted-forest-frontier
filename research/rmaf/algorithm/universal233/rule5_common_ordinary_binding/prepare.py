#!/usr/bin/env python3
"""One-shot thin source/olean extension over two frozen DEVELOPMENT releases.
Use existing byte inventories and producer instrument unchanged; no raw record
copy and no new whole-pool scientific build claim.
"""
from pathlib import Path
import hashlib,json,re,shutil
D=Path(__file__).resolve().parent;R=D.parents[4];O=D/'build';O.mkdir(exist_ok=True)
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
def exact(a,b):
 if a!=b:raise ValueError('EXACT_BYTE_MISMATCH')
# Literal source/hash/collision plants precede frozen input processing.
assert hashlib.sha256(b'abc').hexdigest()=='ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad'
controls={'clean_hash':'PASS','duplicate_clean':'PASS'};exact(b'def a := 3',b'def a := 3')
for tag,a,b in [('changed_bytes',b'abc',b'abd'),('body_collision',b'def a := 3',b'def a := 4')]:
 try:exact(a,b)
 except ValueError:controls[tag]='CAUGHT'
 else:raise AssertionError(tag)
if shutil.disk_usage(D).free<3*1024**3:raise RuntimeError('DISK_FLOOR_3_GIB')
P=R/'research/rmaf/algorithm/universal233/rule5_common_selector_consumer';PM=P/'FINAL-MANIFEST-v1.json';assert sha(PM)=='27fd324fe79c950f3558d63ad805d5e23ead328b667d32787f9a854175e7b312';manifest=json.loads(PM.read_text());pins={e['path']:e['sha256'] for e in manifest['immutable_files']}
S=R/manifest['canonical_receipt']['receipt'];c=json.loads((S/'certificate.json').read_text());assert c['status']=='PASS_AUTHOR_ACTUAL_ONE_SOURCE_CONSUMER_OPEN'
L=R/'research/rmaf/algorithm/universal233/ordinary_dispatch/resume_20261015T1810Z/local_ih_release_v1/LOCAL-IH-MANIFEST-v1.json';assert sha(L)=='1b9e3debeb558e6ec8a8f526cd6e78668f66d4668bff6c9042739eb4e01d6fff';lm=json.loads(L.read_text());lpins={e['path']:e['sha256'] for e in lm['immutable_files']};LS=R/lm['canonical_source_replay']
deps=[]
for e in c['source_entries']:
 n=e['module'];paths=[S/(n+'.lean'),S/(n+'.olean')]
 for p in paths:assert sha(p)==pins[str(p.relative_to(R))];shutil.copyfile(p,O/p.name)
 deps.append({'module':n,'source':str(paths[0].relative_to(R)),'source_sha256':sha(paths[0]),'olean':str(paths[1].relative_to(R)),'olean_sha256':sha(paths[1]),'origin':'frozen_selector315','adaptations':{}})
seen=set();added=[]
def local(n):
 if n in seen:return
 seen.add(n);p=LS/(n+'.lean');assert sha(p)==lpins[str(p.relative_to(R))]
 dest=O/(n+'.lean')
 if dest.exists():exact(p.read_bytes(),dest.read_bytes());return
 for imp in re.findall(r'(?m)^import (\w+)$',p.read_text()):
  if imp not in ['Std','Lean']:local(imp)
 dest.write_bytes(p.read_bytes());added.append({'module':n,'source':str(p.relative_to(R)),'sha256':sha(p),'adaptations':{},'origin':'frozen_local_ih92'})
local('ForestMinimumCompletion')
assert [e['module'] for e in added]==['ForestMinimumCompletion']
for n in ['instrument.py','pilot.py']:
 p=P/n;assert sha(p)==pins[str(p.relative_to(R))];(D/n).write_bytes(p.read_bytes())
pre=json.loads((P/'PRODUCER-PREFLIGHT-v1.json').read_text());m=R/pre['manifest'];assert sha(m)==pre['sha256'];pc=json.loads(m.read_text());assert pc['instrument_sha256']==sha(D/'instrument.py')
for e in pc['immutable_files']:assert sha(R/e['path'])==e['sha256']
(O/'lean-toolchain').write_bytes((S/'lean-toolchain').read_bytes())
rec={'status':'PASS_THIN_FROZEN_EXTENSION_PREPARE','controls':controls,'selector_manifest':{'path':str(PM.relative_to(R)),'sha256':sha(PM)},'local_ih_manifest':{'path':str(L.relative_to(R)),'sha256':sha(L)},'frozen_dependencies':deps,'new_source_inputs':added,'local_imports_checked_identical':sorted(seen-{'ForestMinimumCompletion'}),'producer_preflight':pre,'instrument_sha256':sha(D/'instrument.py'),'pilot_sha256':sha(D/'pilot.py'),'independent_credit':0,'main_milestones':'ALL_OPEN'}
(D/'INPUTS-v1.json').write_text(json.dumps(rec,indent=2)+'\n');(D/'PRODUCER-PREFLIGHT-v1.json').write_text(json.dumps(pre,indent=2)+'\n');print(rec['status'],len(deps),'pinned source/olean dependencies;',len(added),'new frozen source module')
