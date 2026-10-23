#!/usr/bin/env python3
"""Packaging only. Reuses own X0/READY seal design; no scientific rerun."""
import datetime,gzip,hashlib,json,shutil,tarfile
from pathlib import Path
P=Path(__file__).resolve().parent;BASE=P.parent;ROOT=Path('/Users/paurel/Documents/ChatGPT/bootscience')
D=BASE/'sol-review-CONFIRMED-v1';A=BASE/'sol-review-CONFIRMED-v1.tar.gz';S=BASE/'sol-review-CONFIRMED-v1.ARCHIVE-SEAL.json'
if any(q.exists()for q in[D,A,S]):raise SystemExit('Refusing to replace existing scoped review seal')
def h(p):
 q=hashlib.sha256()
 with p.open('rb')as f:
  for b in iter(lambda:f.read(1048576),b''):q.update(b)
 return q.hexdigest()
def meta(p):return{'path':str(p),'bytes':p.stat().st_size,'sha256':h(p)}
def write(p,o):p.write_text(json.dumps(o,indent=2,sort_keys=True)+'\n')
required=['author-manifest-integrity-v1.json','build-pilot-v1.json','build-remaining-v1.json','batch-audit-planted-controls-v1.json','full-origin-axiom-audit-v1.json','exact-adapters-and-adoption-v1.json','accepted-GE-source-adoption-provenance-v1.json','compiled-control-comparison-v1.json','compiled-mass-comparison-v1.json','runtime-oracle-separation-v1.json','reused-one-cut-and-color-corruption-v1.json','preservation-and-final-input-integrity-v1.json']
for name in required:
 if json.loads((P/name).read_text())['all_pass']is not True:raise SystemExit('Unready receipt '+name)
D.mkdir();mapping=[];omitted=[]
for src in sorted(P.rglob('*')):
 if not src.is_file():continue
 rel=src.relative_to(P)
 if 'build'in rel.parts or '__pycache__'in rel.parts or src.suffix=='.pyc':
  omitted.append({**meta(src),'reason':'Fresh compiled scientific/helper binary or routine cache; hash retained, not copied'});continue
 dst=D/'review'/rel;dst.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(src,dst)
 if h(src)!=h(dst):raise SystemExit('Copy mismatch '+str(rel))
 mapping.append({'source':str(src),'snapshot':str(dst.relative_to(D)),'sha256':h(src)})
inputs=[
 ('research/rmaf/algorithm/universal233/pair_assembly/PAIR-ASSEMBLY-MANIFEST-v1.json','provenance/author-manifest.json'),
 ('results/algorithm-universal233-pair-assembly-20261015T093218Z/certificate.json','provenance/canonical-author-certificate.json'),
 ('research/rmaf/algorithm/universal233/pair_assembly/STACK-PINS.json','provenance/author-stack-pins.json'),
 ('research/rmaf/algorithm/verification/pair-case-2026-10-15/frozen-review-v2/MANIFEST.json','provenance/accepted-GE-v2-manifest.json'),
 ('research/rmaf/algorithm/universal233/assembly_completion/ASSEMBLY-COMPLETION-MANIFEST-v1.json','provenance/assembly-completion-manifest.json'),
 ('research/rmaf/algorithm/universal233/assembly/ASSEMBLY-MANIFEST-v1.json','provenance/assembly-manifest.json'),
 ('research/rmaf/algorithm/verification/pair-case-2026-10-15/frozen-review-v2/isolated-review-v1/joint/Restriction.lean','original-adapters/G-E/Restriction.lean'),
 ('research/rmaf/algorithm/verification/pair-case-2026-10-15/frozen-review-v2/isolated-review-v1/joint/Cluster.lean','original-adapters/G-E/Cluster.lean'),
 ('research/rmaf/algorithm/universal233/cut_realization/replay/20261015T080042Z/Coverage.lean','original-adapters/cut/Coverage.lean'),
 ('research/rmaf/algorithm/universal233/cut_realization/replay/20261015T080042Z/InitialCoverage.lean','original-adapters/cut/InitialCoverage.lean'),
 ('research/rmaf/algorithm/verification/good-pair-consumer-2026-10-15/TARGET-v1.md','provenance/root-review-target-v1.md')]
for path,rel in inputs:
 src=ROOT/path;dst=D/rel;dst.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(src,dst);mapping.append({'source':str(src),'snapshot':rel,'sha256':h(src)})
write(D/'PACKAGING-PROVENANCE.json',{'created_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'operation':'Snapshot completed scoped review only; no scientific rerun','source_snapshot_map':mapping,'omitted_compiled_binary_identities':omitted,'scientific_scope':'SCOPED-CONFIRMED local source-bound good-parent consumer only','additional_replications':0,'all_three_main_milestones':'OPEN','immutability':'Read-only snapshot with SHA256 seals; no WORM/trusted-timestamp claim'})
entries=[{'path':q.relative_to(D).as_posix(),'bytes':q.stat().st_size,'sha256':h(q)}for q in sorted(D.rglob('*'))if q.is_file()]
write(D/'MANIFEST.json',{'schema':'good-parent-pair-consumer-independent-review/v1','verdict':'SCOPED-CONFIRMED','entry_count':len(entries),'entries':entries,'additional_replications':0,'all_three_main_milestones':'OPEN'})
(D/'FILES.sha256').write_text(''.join(e['sha256']+'  '+e['path']+'\n'for e in entries))
write(D/'SEAL.json',{'schema':'good-parent-pair-consumer-scoped-review-seal/v1','manifest_sha256':h(D/'MANIFEST.json'),'checksum_list_sha256':h(D/'FILES.sha256'),'entry_count':len(entries),'verdict':'SCOPED-CONFIRMED','additional_replications':0,'all_three_main_milestones':'OPEN'})
for q in D.rglob('*'):
 if q.is_file():q.chmod(0o444)
for q in sorted([q for q in D.rglob('*')if q.is_dir()],reverse=True):q.chmod(0o555)
D.chmod(0o555)
with A.open('wb')as raw:
 with gzip.GzipFile(filename='',mode='wb',fileobj=raw,mtime=0)as gz:
  with tarfile.open(fileobj=gz,mode='w',format=tarfile.PAX_FORMAT)as tf:
   for q in[D]+sorted(D.rglob('*')):
    ti=tf.gettarinfo(str(q),arcname=(Path(D.name)/q.relative_to(D)).as_posix());ti.uid=ti.gid=0;ti.uname=ti.gname='';ti.mtime=0;ti.pax_headers={}
    if q.is_file():
     with q.open('rb')as f:tf.addfile(ti,f)
    else:tf.addfile(ti)
A.chmod(0o444)
seal={'schema':'good-parent-pair-consumer-scoped-archive-seal/v1','verdict':'SCOPED-CONFIRMED','manifest':meta(D/'MANIFEST.json'),'snapshot_seal':meta(D/'SEAL.json'),'archive':meta(A),'additional_replications':0,'all_three_main_milestones':'OPEN'}
write(S,seal);S.chmod(0o444);print(json.dumps(seal,indent=2,sort_keys=True))
