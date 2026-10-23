#!/usr/bin/env python3
"""Final source/fixture/control/result/log snapshot; no scientific execution."""
from pathlib import Path
import datetime,gzip,hashlib,json,shutil,tarfile
P=Path(__file__).resolve().parent;BASE=P.parent;ROOT=Path('/Users/paurel/Documents/ChatGPT/bootscience')
D=BASE/'sol-review-CONFIRMED-v1';A=BASE/'sol-review-CONFIRMED-v1.tar.gz';AS=BASE/'sol-review-CONFIRMED-v1.ARCHIVE-SEAL.json'
if any(p.exists()for p in [D,A,AS]):raise SystemExit('Refusing to replace an existing review seal')
def h(p):
 d=hashlib.sha256()
 with p.open('rb')as f:
  for b in iter(lambda:f.read(1048576),b''):d.update(b)
 return d.hexdigest()
def meta(p):return {'path':str(p),'bytes':p.stat().st_size,'sha256':h(p)}
def save(p,o):p.write_text(json.dumps(o,indent=2,sort_keys=True)+'\n')
required=['source-integrity-v1.json','build-pilot-v1.json','build-remaining-v1.json','compiled-primitive-comparison-v1.json','compiled-battery-comparison-v1.json','compiled-separation-comparison-v1.json','final-literal-malformed-pin-controls-v1.json','audit-planted-comparison-v1.json','producer-data-controls-comparison-v1.json','producer-data-scientific-comparison-v1.json','producer-adoption-comparison-v4.json','actual-imported-dependency-identity-v1.json','consumer-interface-trace-v1.json','final-input-and-preservation-integrity-v1.json']
for n in required:
 if json.loads((P/n).read_text())['all_pass']is not True:raise SystemExit('Unready receipt '+n)
verdict=json.loads((P/'VERDICT-v1.json').read_text())
if verdict['verdict']!='SCOPED-CONFIRMED'or verdict['all_three_main_milestones']!='OPEN'or verdict['additional_replications']!=0:raise SystemExit('Unexpected scope/verdict')
manifest=json.loads((P/'author-manifest.json').read_text());receipt=json.loads((P/'canonical-author-certificate.json').read_text())
for e in manifest['immutable_files']:
 s=ROOT/e['path']
 if not s.is_file()or s.stat().st_size!=e['bytes']or h(s)!=e['sha256']:raise SystemExit('Changed released author file '+e['path'])
for e in receipt['upstream_manifests']:
 if h(ROOT/e['path'])!=e['sha256']:raise SystemExit('Changed upstream pin '+e['path'])
D.mkdir();mapping=[];omitted=[]
def copy(s,rel):
 t=D/rel;t.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(s,t)
 if h(s)!=h(t):raise SystemExit('Snapshot mismatch '+str(rel))
 mapping.append({'source':str(s),'snapshot':str(rel),'sha256':h(s)})
for s in sorted(P.rglob('*')):
 if not s.is_file():continue
 rel=s.relative_to(P)
 if 'build'in rel.parts or '__pycache__'in rel.parts or s.suffix=='.pyc':
  omitted.append({**meta(s),'reason':'Fresh scientific/producer/helper binary or ordinary cache; identity retained without bulky binary'});continue
 copy(s,Path('review')/rel)
# Include the unchanged reference snapshot so relative reference-data paths also work from review/.
READY=BASE/'sol-preparation-READY-v1'
for s in sorted(READY.rglob('*')):
 if s.is_file():copy(s,Path(READY.name)/s.relative_to(READY))
# Preserve every released author source/failed attempt/log/receipt as frozen provenance.
for e in manifest['immutable_files']:copy(ROOT/e['path'],Path('author-freeze/root')/e['path'])
copy(ROOT/'research/rmaf/algorithm/universal233/binary_cheap/BINARY-CHEAP-MANIFEST-v1.json',Path('author-freeze/BINARY-CHEAP-MANIFEST-v1.json'))
for e in receipt['upstream_manifests']:copy(ROOT/e['path'],Path('provenance/root')/e['path'])
copy(BASE/'TARGET-v1.md',Path('provenance/root-review-TARGET-v1.md'))
copy(BASE/'sol-preparation-READY-v1.ARCHIVE-SEAL.json',Path('provenance/READY-ARCHIVE-SEAL.json'))
(D/'README.txt').write_text('SCOPED-CONFIRMED binary-cheap graph/local-certificate/raw-list interface. Read review/FINAL-REPORT-v1.md, review/ERRATUM-ORIGIN-AUDIT-v1.md and review/VERDICT-v1.json. The original REPORT-v1.md is the incremental journal. All3 main milestones OPEN; zero additional replications. No actual query/whole-source cut union/source runtime/full algorithm acceptance. Fresh-context referee remains separate. All author files and the unchanged READY reference snapshot are retained. Compiled binaries are omitted with hashes/dependency identities in PACKAGING-PROVENANCE.json. Read-only SHA256 snapshot; no WORM/trusted-timestamp claim.\n')
save(D/'PACKAGING-PROVENANCE.json',{'created_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'operation':'Final immutable copy only; no scientific rerun','source_snapshot_map':mapping,'omitted_binary_identities':omitted,'verdict':'SCOPED-CONFIRMED','author_manifest_sha256':h(P/'author-manifest.json'),'preserved_READY_manifest_sha256':h(READY/'MANIFEST.json'),'producer_audit_correction':'3590 merged distinct names;3616 stored producer occurrences;339 private;no custom axioms','all_three_main_milestones':'OPEN','additional_replications':0,'immutability':'Read-only SHA256 snapshot, no WORM or trusted-timestamp claim'})
entries=[{'path':p.relative_to(D).as_posix(),'bytes':p.stat().st_size,'sha256':h(p)}for p in sorted(D.rglob('*'))if p.is_file()]
save(D/'MANIFEST.json',{'schema':'binary-cheap-independent-scoped-review/v1','verdict':'SCOPED-CONFIRMED','entry_count':len(entries),'entries':entries,'all_three_main_milestones':'OPEN','additional_replications':0,'audit_erratum':'review/ERRATUM-ORIGIN-AUDIT-v1.md'})
(D/'FILES.sha256').write_text(''.join(e['sha256']+'  '+e['path']+'\n'for e in entries))
save(D/'SEAL.json',{'schema':'binary-cheap-scoped-review-seal/v1','verdict':'SCOPED-CONFIRMED','entry_count':len(entries),'manifest_sha256':h(D/'MANIFEST.json'),'checksum_list_sha256':h(D/'FILES.sha256'),'all_three_main_milestones':'OPEN','additional_replications':0})
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
seal={'schema':'binary-cheap-scoped-review-archive-seal/v1','verdict':'SCOPED-CONFIRMED','entry_count':len(entries),'manifest':meta(D/'MANIFEST.json'),'snapshot_seal':meta(D/'SEAL.json'),'archive':meta(A),'all_three_main_milestones':'OPEN','additional_replications':0}
save(AS,seal);AS.chmod(0o444);print(json.dumps(seal,indent=2,sort_keys=True))
