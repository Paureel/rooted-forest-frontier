"""One-shot immutable finite author source-pool release, retaining all failures."""
from pathlib import Path
import datetime,hashlib,json,time
D=Path(__file__).resolve().parent;R=D.parents[5];O=D/'pool_release_v1'
B=R/'results/algorithm-universal233-ordinary-source-pool-20261015T144445575127Z'
A=R/'results/algorithm-universal233-ordinary-source-pool-compressed-20261015T182814513546Z'
def sha(p):
 h=hashlib.sha256()
 with p.open('rb') as f:
  for b in iter(lambda:f.read(1<<20),b''):h.update(b)
 return h.hexdigest()
c=json.loads((A/'certificate.json').read_text());assert c['status']=='PASS_AUTHOR_COMPRESSED_POOL_AUDIT' and c['source_modules']==306 and c['stored_producer_occurrences']==8493
assert len(c['saved_producers'])==206 and len(c['new_producers'])==100 and c['compressed_bytes']==2465461
files=list(O.rglob('*'))+list(B.rglob('*'))
for p in (R/'results').glob('algorithm-universal233-ordinary-source-pool-resume-*'):files.extend(p.rglob('*'))
for p in (R/'results').glob('algorithm-universal233-ordinary-source-pool-compressed-*'):files.extend(p.rglob('*'))
for n in ['resume_pool_audit.py','compressed_pool_resume.py','compressed_pool_resume_v2.py','compressed_pool_resume_v3.py','AUDIT-PLAN-v1.md','COMPRESSED-AUDIT-AMENDMENT-v1.md','COMPRESSED-HEADER-ERRATUM-v1.md','PROOF-TEXT-SCOPE-v3.md']:files.append(D/n)
for n in ['prepare_pool.py','audit_pool.py','audit_pool-v1-failed.py.txt','INPUT-INVENTORY-v1.json','PRECONSTRUCTION-PIN-v1.json']:files.append(D.parent/'source_pool'/n)
files=sorted({p for p in files if p.is_file()});rows=[];started=time.monotonic()
for i,p in enumerate(files):
 rows.append(dict(path=str(p.relative_to(R)),sha256=sha(p)))
 if i%250==0:print('PINNED',i,'OF',len(files),flush=True)
rec=dict(version=1,utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),status='FINITE_AUTHOR_SOURCE_POOL_COMPATIBILITY',no_further_writes=True,all_main_milestones='OPEN',novelty='OPEN',independent_acceptance=False,source_modules=306,stored_producer_occurrences=8493,axiom_union=c['axiom_union'],saved_raw_producers=206,new_compressed_producers=100,new_compressed_bytes=2465461,proof_text_scope=c['source_build_claim'],compiled_runtime_claim=False,universal_rule_coverage=False,canonical_source_construction=str(B.relative_to(R)),canonical_producer_audit=str(A.relative_to(R)),immutable_files=rows)
m=O/'SOURCE-POOL-MANIFEST-v1.json';m.write_text(json.dumps(rec,indent=2)+'\n')
for p in files+[m]:p.chmod(0o444)
print(json.dumps(dict(manifest=str(m.relative_to(R)),sha256=sha(m),members=len(rows),pin_seconds=time.monotonic()-started)))
