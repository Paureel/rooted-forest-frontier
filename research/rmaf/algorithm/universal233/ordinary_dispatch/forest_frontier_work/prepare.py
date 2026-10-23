#!/usr/bin/env python3
"""Pin literal frozen forest closure and report exact shared-module identity."""
from pathlib import Path
import datetime,hashlib,json,os,shutil
D=Path(__file__).resolve().parent;R=next(p for p in D.parents if (p/'bootloops-lean').exists());sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
def exact(a,b):
 if a!=b:raise ValueError('SOURCE_BYTE_MISMATCH')
assert hashlib.sha256(b'abc').hexdigest()=='ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad';exact(b'import X\ndef a := 1',b'import X\ndef a := 1');controls={'known_hash':'PASS','exact_duplicate':'PASS'}
for k,a,b in [('changed_body',b'import X\ndef a := 1',b'import X\ndef a := 2'),('changed_import',b'import X\ndef a := 1',b'import Y\ndef a := 1')]:
 try:exact(a,b)
 except ValueError:controls[k]='CAUGHT'
 else:raise AssertionError('PLANT_FAILED')
try:{}['missing']
except KeyError:controls['missing_source']='CAUGHT'
else:raise AssertionError('MISSING_PLANT_FAILED')
assert shutil.disk_usage(D).free>=3*1024**3
mp='research/rmaf/algorithm/universal233/forest_solver/FOREST-SOLVER-MANIFEST-v3.json';mh='89937a6f71bceb2dbeb64917b4b805e8f193fa485b00ec28acecdc95d047dcf5';M=R/mp;assert sha(M)==mh;m=json.loads(M.read_text());pins={e['path']:e['sha256'] for e in m['immutable_files']};S=R/m['canonical_receipt'];sources={}
for p in S.glob('*.lean'):
 n=p.stem;o=p.with_suffix('.olean')
 if str(p.relative_to(R)) not in pins or str(o.relative_to(R)) not in pins:continue
 row={'module':n,'files':[]}
 for f in [p,o]:
  h=pins[str(f.relative_to(R))];assert sha(f)==h;row['files'].append({'original':str(f.relative_to(R)),'sha256':h,'original_mode':oct(f.stat().st_mode&0o777)})
 sources[n]=row
seeds=['ForestWorkBound','QueryWork'];todo=list(seeds);chosen={}
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
# Canonical forest closure is self-contained; inspect exact common bodies before any union.
pp='research/rmaf/algorithm/universal233/ordinary_dispatch/fast_source_pool/release_v1/FAST-SOURCE-POOL-MANIFEST-v1.json';ph='efa132be64d489544e2aeeffaa0d08494cb9986d28104024f200f1080e2fbb60';assert sha(R/pp)==ph;pool=json.loads((R/pp).read_text());poolpins={e['path']:e['sha256'] for e in pool['immutable_files']};P=R/'results/algorithm-universal233-fast-source-pool-20261015T194053203759Z';shared=[];mismatches=[]
for n,e in sorted(chosen.items()):
 p=P/(n+'.lean')
 if not p.exists():continue
 assert sha(p)==poolpins[str(p.relative_to(R))]
 a=(R/e['files'][0]['original']).read_bytes();b=p.read_bytes()
 if a==b:shared.append({'module':n,'forest':e['files'][0],'pool_source':str(p.relative_to(R)),'sha256':sha(p)})
 else:mismatches.append({'module':n,'forest':e['files'][0],'pool_source':str(p.relative_to(R)),'pool_sha256':sha(p)})
# A canonical standalone root remains valid; no mismatched pool module is silently consumed.
O=R/'results'/('algorithm-universal233-forest-frontier-root-'+datetime.datetime.now(datetime.timezone.utc).strftime('%Y%m%dT%H%M%SZ'));O.mkdir();deps=[]
for n,e in sorted(chosen.items()):
 for f in e['files']:
  p=R/f['original'];q=O/p.name
  if p.stat().st_mode&0o222:shutil.copyfile(p,q);q.chmod(0o444);kind='EXACT_READONLY_COPY_FROM_WRITABLE_MODE_FROZEN_BYTES'
  else:os.link(p,q);kind='READONLY_HARDLINK'
  assert sha(q)==f['sha256'] and not q.stat().st_mode&0o222
  f.update(linked=str(q.relative_to(R)),inode=q.stat().st_ino,device=q.stat().st_dev,snapshot_kind=kind)
 deps.append(e)
(O/'lean-toolchain').write_bytes((S/'lean-toolchain').read_bytes())
I=R/'research/rmaf/algorithm/universal233/rule5_common_selector_consumer/instrument.py';assert sha(I)=='91b8125cfd2f150c9868c2605206682102bf82e5a92addad5fb49b678cc69cc5';(D/'instrument.py').write_bytes(I.read_bytes());pre={'manifest':'results/algorithm-universal233-rule5-common-selector-producer-20261015T184716Z/manifest.json','sha256':'5212b42867ec05b7fe1e5d2eb4d65e8a4ae84e9528f1f0c3ab40b50089b1e829'};assert sha(R/pre['manifest'])==pre['sha256'];pc=json.loads((R/pre['manifest']).read_text());assert pc['instrument_sha256']==sha(D/'instrument.py')
for e in pc['immutable_files']:assert sha(R/e['path'])==e['sha256']
rec={'status':'PASS_EXACT_CANONICAL_FOREST_CLOSURE','root':str(O.relative_to(R)),'controls':controls,'seeds':seeds,'dependencies':deps,'manifests':[{'path':mp,'sha256':mh},{'path':pp,'sha256':ph}],'shared_exact_pool_sources':shared,'shared_name_mismatches_not_consumed':mismatches,'source_union':'No pool bytes consumed; canonical frozen forest source/olean closure only. Any future union must resolve listed exact source mismatches.','instrument_sha256':sha(D/'instrument.py'),'producer_preflight':pre,'independent_credit':0,'main_milestones':'ALL_OPEN'}
(D/'ROOT-v1.json').write_text(json.dumps(rec,indent=2)+'\n');print(rec['status'],len(deps),'readonly pairs;',len(shared),'exact shared sources;',len(mismatches),'unconsumed mismatches;',O,flush=True)
