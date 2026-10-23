# One-shot immutable seal; scientific extractor/compatibility tools are unchanged.
from pathlib import Path
import datetime,hashlib,json
D=Path(__file__).resolve().parent;R=D.parents[5];B=R/'results/algorithm-universal233-fast-source-pool-20261015T194053203759Z';A=R/'results/algorithm-universal233-fast-source-audit-20261015T195353361662Z';F=R/'results/algorithm-universal233-fast-source-pool-20261015T193914589171Z'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
c=json.loads((A/'certificate.json').read_text());assert c['status']=='PASS_AUTHOR_FAST_CONSUMER_ONE_ROOT_SOURCE_PRODUCER_AUDIT' and c['stored_producer_occurrences']==9097 and c['source_modules']==380
assert len(c['reused_producers'])==221 and len(c['new_producers'])==161
for p,h in json.loads((A/'BUILD-PINS.json').read_text()).items():assert sha(R/p)==h
files=sorted({p for root in [D,B,A,F] if root.exists() for p in root.rglob('*') if p.is_file()});rows=[dict(path=str(p.relative_to(R)),sha256=sha(p)) for p in files]
m=D/'release_v1/FAST-SOURCE-POOL-MANIFEST-v1.json';assert not m.exists();r=dict(version=1,utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),status='AUTHOR_ACTUAL_FAST_CONSUMER_ONE_ROOT_SOURCE_COMPATIBILITY',no_further_writes=True,all_main_milestones='OPEN',novelty='OPEN',independent_acceptance=False,full_faster_solver=False,source_bit_payload_runtime='OPEN',canonical_build=str(B.relative_to(R)),canonical_audit=str(A.relative_to(R)),fresh_source_builds=380,master_imports=2,selected_stored_occurrences=9097,exact_binary_record_reuse=221,new_producer_extractions=161,axiom_union=c['axiom_union'],immutable_files=rows);m.write_text(json.dumps(r,indent=2)+'\n')
for p in files+[m]:p.chmod(0o444)
for e in rows:assert sha(R/e['path'])==e['sha256']
print(json.dumps(dict(manifest=str(m.relative_to(R)),sha256=sha(m),members=len(rows))))
