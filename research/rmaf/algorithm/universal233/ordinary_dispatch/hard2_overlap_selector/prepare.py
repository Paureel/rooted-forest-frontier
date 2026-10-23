#!/usr/bin/env python3
"""One-shot readonly hard-link dependency root; no dependency is recompiled.
Use completed selector315 source/olean pins, retaining exact inode/path hashes.
"""
from pathlib import Path
import datetime,hashlib,json,os,shutil
D=Path(__file__).resolve().parent;R=next(p for p in D.parents if (p/'bootloops-lean').exists());sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
def exact(a,b):
 if a!=b:raise ValueError('SOURCE_BYTE_MISMATCH')
assert hashlib.sha256(b'abc').hexdigest()=='ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad';exact(b'fixed',b'fixed');controls={'clean_hash':'PASS','duplicate_clean':'PASS'}
for tag,a,b in [('changed_bytes',b'abc',b'abd'),('changed_body',b'def a := 3',b'def a := 4')]:
 try:exact(a,b)
 except ValueError:controls[tag]='CAUGHT'
 else:raise AssertionError(tag)
free=shutil.disk_usage(D).free
if free<3*1024**3:raise RuntimeError(('DISK_FLOOR_3_GIB',free))
P=R/'research/rmaf/algorithm/universal233/rule5_common_selector_consumer';M=P/'FINAL-MANIFEST-v1.json';assert sha(M)=='27fd324fe79c950f3558d63ad805d5e23ead328b667d32787f9a854175e7b312';m=json.loads(M.read_text());pins={e['path']:e['sha256'] for e in m['immutable_files']};S=R/m['canonical_receipt']['receipt'];c=json.loads((S/'certificate.json').read_text())
O=R/'results'/('algorithm-universal233-ordinary-hard2-overlap-root-'+datetime.datetime.now(datetime.timezone.utc).strftime('%Y%m%dT%H%M%SZ'));O.mkdir();deps=[]
for e in c['source_entries']:
 n=e['module'];row={'module':n,'files':[]}
 for suffix in ['.lean','.olean']:
  p=S/(n+suffix);h=pins[str(p.relative_to(R))];assert sha(p)==h;assert not p.stat().st_mode&0o222;q=O/p.name;os.link(p,q);assert q.stat().st_ino==p.stat().st_ino
  row['files'].append({'original':str(p.relative_to(R)),'linked':str(q.relative_to(R)),'sha256':h,'inode':p.stat().st_ino,'device':p.stat().st_dev})
 deps.append(row)
(O/'lean-toolchain').write_bytes((S/'lean-toolchain').read_bytes())
for n in ['instrument.py']:
 p=P/n;assert sha(p)==pins[str(p.relative_to(R))];(D/n).write_bytes(p.read_bytes())
pre=json.loads((P/'PRODUCER-PREFLIGHT-v1.json').read_text());assert sha(R/pre['manifest'])==pre['sha256'];pm=json.loads((R/pre['manifest']).read_text());assert pm['instrument_sha256']==sha(D/'instrument.py')
for e in pm['immutable_files']:assert sha(R/e['path'])==e['sha256']
rec={'status':'PASS_IMMUTABLE_HARDLINK_ROOT','root':str(O.relative_to(R)),'controls':controls,'frozen_manifest':{'path':str(M.relative_to(R)),'sha256':sha(M)},'dependencies':deps,'producer_preflight':pre,'instrument_sha256':sha(D/'instrument.py'),'no_dependency_compilation':True,'initial_free_bytes':free,'independent_credit':0,'main_milestones':'ALL_OPEN'}
(D/'ROOT-v1.json').write_text(json.dumps(rec,indent=2)+'\n');print(rec['status'],len(deps),'dependency modules;',free,'free bytes',O)
