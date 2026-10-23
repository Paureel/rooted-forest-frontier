# One-shot immutable same-author DP component seal after scoped actual audit.
from pathlib import Path
import datetime,hashlib,json
D=Path(__file__).resolve().parent;R=D.parents[5]
def sha(p):
 h=hashlib.sha256()
 with p.open('rb') as f:
  for b in iter(lambda:f.read(1<<20),b''):h.update(b)
 return h.hexdigest()
B=R/json.loads((D/'LATEST-BUILD-v1.json').read_text())['directory'];A=R/json.loads((D/'LATEST-AUDIT-v1.json').read_text())['directory'];c=json.loads((A/'certificate.json').read_text())
assert c['status']=='PASS_AUTHOR_ACTUAL_ALLGOOD_DP_SOURCE_WORK_PRODUCER'
assert c['actual_imported_modules']==486 and c['new_own_builds']==9 and c['fresh_actual_producers']==18 and c['selected_stored_occurrences']==12235
assert len(c['reused_producers'])==468 and len(c['new_producers'])==18
for p,h in c['inputs'].items():assert sha(R/p)==h,p
for p,h in json.loads((A/'BUILD-PINS.json').read_text()).items():assert sha(R/p)==h,p
for e in c['reused_producers']+c['new_producers']:assert sha(R/e['path'])==e['sha256']
roots=[D,B]+list((R/'results').glob('algorithm-universal233-allgood-local-work-audit-*'))
files=sorted({p for root in roots for p in root.rglob('*') if p.is_file() and '__pycache__' not in p.parts})
for p in files:assert not (p.stat().st_nlink>1 and p.stat().st_mode&0o222),('WRITABLE_SHARED_INODE',str(p))
rows=[dict(path=str(p.relative_to(R)),sha256=sha(p)) for p in files];m=D/'ALLGOOD-WORK-MANIFEST-v1.json';assert not m.exists()
record=dict(version=1,utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),status='AUTHOR_ACTUAL_ALLGOOD_DP_UNIT_SOURCE_WORK_POLYNOMIAL',no_further_writes=True,all_main_milestones='OPEN',novelty='OPEN',independent_acceptance=False,full_source_bit_payload_recurrence='OPEN',full_runtime_claim=False,unit_source_work_bound='1048576*(n+1)^4 under actual proper state',scalar_scope='Unit structural/source slots; native binary/IR correspondence not proved',canonical_build=str(B.relative_to(R)),canonical_audit=str(A.relative_to(R)),certificate_sha256=sha(A/'certificate.json'),new_source_modules=9,fresh_actual_producers=18,new_stored_occurrences=c['new_stored_occurrences'],actual_imported_modules=486,selected_stored_occurrences=12235,axiom_union=c['axiom_union'],interfaces=c['interfaces'],immutable_files=rows)
m.write_text(json.dumps(record,indent=2)+'\n')
for p in files+[m]:p.chmod(0o444)
for e in rows:assert sha(R/e['path'])==e['sha256']
print(json.dumps(dict(manifest=str(m.relative_to(R)),sha256=sha(m),members=len(rows))))
