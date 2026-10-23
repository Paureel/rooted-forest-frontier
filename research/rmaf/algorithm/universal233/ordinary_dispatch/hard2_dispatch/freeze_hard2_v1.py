# One-shot problem-specific seal; scientific checks ran in the pinned audit first.
from pathlib import Path
import datetime, hashlib, json
D=Path(__file__).resolve().parent
R=D.parents[5]
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
B=R/json.loads((D/'LATEST-BUILD-v1.json').read_text())['directory']
A=R/json.loads((D/'LATEST-AUDIT-v1.json').read_text())['directory']
c=json.loads((A/'certificate.json').read_text())
assert c['status']=='PASS_AUTHOR_LITERAL_HARD2_DISPATCH_SOURCE_PRODUCER'
assert c['imported_modules']==420 and c['selected_stored_occurrences']==10052
assert c['new_own_builds']==6 and c['freshly_extracted_modules']==38
assert len(c['reused_producers'])==382 and len(c['new_producers'])==38
assert c['axiom_union']==['Classical.choice','Quot.sound','propext']
for p,h in c['inputs'].items(): assert sha(R/p)==h, p
for p,h in json.loads((A/'BUILD-PINS.json').read_text()).items(): assert sha(R/p)==h, p
for e in c['reused_producers']+c['new_producers']: assert sha(R/e['path'])==e['sha256'], e['path']
files=sorted({p for root in [D,B,A] for p in root.rglob('*') if p.is_file()})
rows=[dict(path=str(p.relative_to(R)),sha256=sha(p)) for p in files]
m=D/'HARD2-DISPATCH-MANIFEST-v1.json'
assert not m.exists()
rec=dict(version=1,utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),
 status='AUTHOR_LITERAL_HARD2_DISPATCH_CURRENT_BUDGET_EXACTNESS',no_further_writes=True,
 all_main_milestones='OPEN',novelty='OPEN',source_bit_payload_runtime='OPEN',
 full_faster_solver=False,independent_acceptance=False,runtime_ghost=False,
 canonical_build=str(B.relative_to(R)),canonical_audit=str(A.relative_to(R)),
 certificate_sha256=sha(A/'certificate.json'),actual_imported_modules=420,
 selected_stored_occurrences=10052,new_own_builds=6,new_own_stored_occurrences=331,
 exact_binary_record_reuse=382,new_producer_extractions=38,axiom_union=c['axiom_union'],
 interfaces=c['interfaces'],immutable_files=rows)
m.write_text(json.dumps(rec,indent=2)+'\n')
for p in files+[m]: p.chmod(0o444)
for e in rows: assert sha(R/e['path'])==e['sha256'], e['path']
print(json.dumps(dict(manifest=str(m.relative_to(R)),sha256=sha(m),members=len(rows))))
