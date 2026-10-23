# One-shot immutable author seal after scoped source-bound audit.
from pathlib import Path
import datetime,hashlib,json
D=Path(__file__).resolve().parent;R=D.parents[5];sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
B=R/json.loads((D/'LATEST-BUILD-v1.json').read_text())['directory'];A=R/json.loads((D/'LATEST-AUDIT-v1.json').read_text())['directory'];c=json.loads((A/'certificate.json').read_text())
assert c['status']=='PASS_AUTHOR_ACTUAL_HARD2_QUERY_SIZE_SOURCE_PRODUCER'
assert c['actual_imported_modules']==427 and c['new_own_builds']==4 and c['new_own_stored_occurrences']==50 and c['selected_stored_occurrences']==10218
assert len(c['reused_producers'])==423
for p,h in c['inputs'].items():assert sha(R/p)==h,p
for p,h in json.loads((A/'BUILD-PINS.json').read_text()).items():assert sha(R/p)==h,p
for e in c['reused_producers']+c['new_producers']:assert sha(R/e['path'])==e['sha256']
roots=[D,B]+list((R/'results').glob('algorithm-universal233-hard2-query-size-audit-*'))
files=sorted({p for root in roots for p in root.rglob('*') if p.is_file() and '__pycache__' not in p.parts});rows=[dict(path=str(p.relative_to(R)),sha256=sha(p)) for p in files]
m=D/'HARD2-SIZE-MANIFEST-v1.json';assert not m.exists()
rec=dict(version=1,utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),status='AUTHOR_ACTUAL_NONRULE5_HARD2_QUERY_SIZE_AND_POTENTIAL',no_further_writes=True,all_main_milestones='OPEN',novelty='OPEN',independent_acceptance=False,full_source_bit_payload_recurrence='OPEN',full_runtime_claim=False,canonical_build=str(B.relative_to(R)),canonical_audit=str(A.relative_to(R)),certificate_sha256=sha(A/'certificate.json'),new_source_modules=4,new_stored_occurrences=50,actual_imported_modules=427,selected_stored_occurrences=10218,axiom_union=c['axiom_union'],interfaces=c['interfaces'],immutable_files=rows)
m.write_text(json.dumps(rec,indent=2)+'\n')
for p in files+[m]:p.chmod(0o444)
for e in rows:assert sha(R/e['path'])==e['sha256']
print(json.dumps(dict(manifest=str(m.relative_to(R)),sha256=sha(m),members=len(rows))))
