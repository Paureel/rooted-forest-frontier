#!/usr/bin/env python3
"""Packaging only, reusing the own-X0 manifest/seal design. No scientific rerun."""
import datetime,gzip,hashlib,json,tarfile
from pathlib import Path
import shutil
P=Path(__file__).resolve().parent.parent;R=P.parent
DEST=R/'sol-preparation-READY-v1';ARCHIVE=R/'sol-preparation-READY-v1.tar.gz';OUT=R/'sol-preparation-READY-v1.ARCHIVE-SEAL.json'
if any(q.exists() for q in [DEST,ARCHIVE,OUT]):raise SystemExit('Refusing to replace a sealed preparation')
def sha(p):
 h=hashlib.sha256()
 with p.open('rb') as f:
  for b in iter(lambda:f.read(1048576),b''):h.update(b)
 return h.hexdigest()
def info(p):return {'path':str(p),'bytes':p.stat().st_size,'sha256':sha(p)}
def write(p,obj):p.write_text(json.dumps(obj,indent=2,sort_keys=True)+'\n')
# Read-only checks of completed receipts, not reruns of their instruments.
requirements=[('graph-controls-v1.json','all_pass'),('graph-pilot-v1.json','all_pass'),('graph-battery-v1.json','all_pass'),('graph-interface-results-v1.json','all_pass'),('toy-battery-v2.json','all_pass'),('old-handoff-preservation-v1.json','all_pass')]
for name,key in requirements:
 if json.loads((P/name).read_text())[key] is not True:raise SystemExit('Unready receipt '+name)
DEST.mkdir();omitted=[];originals=[]
for src in sorted(P.rglob('*')):
 if not src.is_file():continue
 rel=src.relative_to(P)
 if 'toy-build' in rel.parts or '__pycache__'in rel.parts or src.suffix=='.pyc':
  omitted.append({**info(src),'reason':'Fresh toy compiled binary or routine Python cache; hash retained, excluded from source/control handoff'});continue
 dst=DEST/'preparation'/rel;dst.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(src,dst)
 if sha(src)!=sha(dst):raise SystemExit('Copy mismatch '+str(rel))
 originals.append({'source':str(src),'snapshot':str(dst.relative_to(DEST)),'sha256':sha(src)})
for src,rel in [(R/'TARGET-v1.md','root-pin/TARGET-v1.md'),(R/'sol-review-preparation-v1.md','preparation-workfile/sol-review-preparation-v1.md')]:
 dst=DEST/rel;dst.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(src,dst);originals.append({'source':str(src),'snapshot':rel,'sha256':sha(src)})
write(DEST/'PACKAGING-PROVENANCE.json',{'created_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'operation':'Snapshot completed preparation records only; no candidate release/contact/compilation and no scientific rerun','source_snapshot_map':originals,'omitted_files':omitted,'scientific_status':'READY preparation only; exact root release still required','candidate_compilation':False,'candidate_contact':False,'replication_increment':0,'all_three_main_milestones':'OPEN','immutability':'Read-only snapshot plus SHA256 seals; no WORM or trusted timestamp assertion'})
entries=[{'path':q.relative_to(DEST).as_posix(),'bytes':q.stat().st_size,'sha256':sha(q)} for q in sorted(DEST.rglob('*')) if q.is_file()]
write(DEST/'MANIFEST.json',{'schema':'good-pair-consumer-prerelease-preparation/v1','status':'READY; awaiting exact root release','entry_count':len(entries),'entries':entries,'candidate_contact':False,'candidate_compilation':False,'replication_increment':0,'all_three_main_milestones':'OPEN'})
(DEST/'FILES.sha256').write_text(''.join(e['sha256']+'  '+e['path']+'\n' for e in entries))
write(DEST/'SEAL.json',{'schema':'good-pair-consumer-prerelease-seal/v1','status':'READY preparation only; not self-released','manifest_sha256':sha(DEST/'MANIFEST.json'),'checksum_list_sha256':sha(DEST/'FILES.sha256'),'entry_count':len(entries),'all_three_main_milestones':'OPEN','replication_increment':0})
for q in DEST.rglob('*'):
 if q.is_file():q.chmod(0o444)
for q in sorted([q for q in DEST.rglob('*') if q.is_dir()],reverse=True):q.chmod(0o555)
DEST.chmod(0o555)
with ARCHIVE.open('wb') as raw:
 with gzip.GzipFile(filename='',mode='wb',fileobj=raw,mtime=0) as gz:
  with tarfile.open(fileobj=gz,mode='w',format=tarfile.PAX_FORMAT) as tf:
   for q in [DEST]+sorted(DEST.rglob('*')):
    ti=tf.gettarinfo(str(q),arcname=(Path(DEST.name)/q.relative_to(DEST)).as_posix());ti.uid=ti.gid=0;ti.uname=ti.gname='';ti.mtime=0;ti.pax_headers={}
    if q.is_file():
     with q.open('rb') as f:tf.addfile(ti,f)
    else:tf.addfile(ti)
ARCHIVE.chmod(0o444)
seal={'schema':'good-pair-consumer-prerelease-archive-seal/v1','status':'READY preparation only; exact root release pending','manifest':info(DEST/'MANIFEST.json'),'snapshot_seal':info(DEST/'SEAL.json'),'archive':info(ARCHIVE),'candidate_contact':False,'candidate_compilation':False,'replication_increment':0,'all_three_main_milestones':'OPEN'}
write(OUT,seal);OUT.chmod(0o444);print(json.dumps(seal,indent=2,sort_keys=True))
