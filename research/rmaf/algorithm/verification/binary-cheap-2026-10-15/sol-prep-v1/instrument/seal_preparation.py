#!/usr/bin/env python3
"""Packaging only: preserve all preparation versions/receipts; no scientific rerun."""
from pathlib import Path
import datetime,gzip,hashlib,json,shutil,tarfile
P=Path(__file__).resolve().parent.parent;BASE=P.parent
D=BASE/'sol-preparation-READY-v1';A=BASE/'sol-preparation-READY-v1.tar.gz';AS=BASE/'sol-preparation-READY-v1.ARCHIVE-SEAL.json'
if any(p.exists()for p in [D,A,AS]):raise SystemExit('Refusing to replace an existing READY seal')
def h(p):
 d=hashlib.sha256()
 with p.open('rb')as f:
  for b in iter(lambda:f.read(1048576),b''):d.update(b)
 return d.hexdigest()
def meta(p):return {'path':str(p),'bytes':p.stat().st_size,'sha256':h(p)}
def save(p,o):p.write_text(json.dumps(o,indent=2,sort_keys=True)+'\n')
for n in ['graph-pilot-v1.json','graph-battery-v2.json','literal-mutation-results-v1.json','toy-pilot-v1.json','toy-battery-v1.json','preservation-provenance-v1.json','ready-integrity-v1.json']:
 if json.loads((P/n).read_text())['all_pass']is not True:raise SystemExit('Unready receipt '+n)
if json.loads((P/'stdlib-dependency-identity-v1.json').read_text())['missing']:raise SystemExit('Missing standard library dependency identity')
D.mkdir();mapping=[];omitted=[]
for s in sorted(P.rglob('*')):
 if not s.is_file():continue
 rel=s.relative_to(P)
 if 'toy-build'in rel.parts or '__pycache__'in rel.parts or s.suffix=='.pyc':
  omitted.append({**meta(s),'reason':'Compiled toy/helper binary or ordinary cache; exact identity retained, not copied'});continue
 d=D/'preparation'/rel;d.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(s,d)
 if h(d)!=h(s):raise SystemExit('Snapshot copy mismatch '+str(rel))
 mapping.append({'source':str(s),'snapshot':str(d.relative_to(D)),'sha256':h(s)})
target=BASE/'TARGET-v1.md';t=D/'provenance/root-TARGET-v1.md';t.parent.mkdir();shutil.copyfile(target,t)
mapping.append({'source':str(target),'snapshot':str(t.relative_to(D)),'sha256':h(target)})
save(D/'PACKAGING-PROVENANCE.json',{'created_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'operation':'Preparation snapshot only; no scientific rerun','source_snapshot_map':mapping,'omitted_binary_identities':omitted,'verdict':'READY; candidate unread/uncompiled; exact root release pending','additional_replications':0,'all_three_main_milestones':'OPEN','immutability':'Read-only SHA256 snapshot; no WORM or trusted-timestamp claim','old213_109_36':'Preserved and rechecked as recorded in preparation/preservation-provenance-v1.json'})
entries=[{'path':p.relative_to(D).as_posix(),'bytes':p.stat().st_size,'sha256':h(p)}for p in sorted(D.rglob('*'))if p.is_file()]
save(D/'MANIFEST.json',{'schema':'binary-cheap-independent-review-preparation/v1','verdict':'READY','entry_count':len(entries),'entries':entries,'candidate_contact':False,'candidate_compilation':False,'additional_replications':0,'all_three_main_milestones':'OPEN'})
(D/'FILES.sha256').write_text(''.join(e['sha256']+'  '+e['path']+'\n'for e in entries))
save(D/'SEAL.json',{'schema':'binary-cheap-preparation-seal/v1','manifest_sha256':h(D/'MANIFEST.json'),'checksum_list_sha256':h(D/'FILES.sha256'),'entry_count':len(entries),'verdict':'READY','candidate_contact':False,'candidate_compilation':False,'additional_replications':0,'all_three_main_milestones':'OPEN'})
for p in D.rglob('*'):
 if p.is_file():p.chmod(0o444)
for p in sorted([p for p in D.rglob('*')if p.is_dir()],reverse=True):p.chmod(0o555)
D.chmod(0o555)
with A.open('wb')as raw:
 with gzip.GzipFile(filename='',mode='wb',fileobj=raw,mtime=0)as gz:
  with tarfile.open(fileobj=gz,mode='w',format=tarfile.PAX_FORMAT)as tf:
   for p in [D]+sorted(D.rglob('*')):
    ti=tf.gettarinfo(str(p),arcname=(Path(D.name)/p.relative_to(D)).as_posix());ti.uid=ti.gid=0;ti.uname=ti.gname='';ti.mtime=0;ti.pax_headers={}
    if p.is_file():
     with p.open('rb')as f:tf.addfile(ti,f)
    else:tf.addfile(ti)
A.chmod(0o444)
seal={'schema':'binary-cheap-preparation-archive-seal/v1','manifest':meta(D/'MANIFEST.json'),'snapshot_seal':meta(D/'SEAL.json'),'archive':meta(A),'verdict':'READY','candidate_contact':False,'candidate_compilation':False,'additional_replications':0,'all_three_main_milestones':'OPEN'}
save(AS,seal);AS.chmod(0o444);print(json.dumps(seal,indent=2,sort_keys=True))
