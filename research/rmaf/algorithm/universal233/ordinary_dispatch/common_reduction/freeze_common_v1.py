from pathlib import Path
import datetime,hashlib,json
D=Path(__file__).resolve().parent;R=D.parents[5];O=D/'release_v1';B=R/'results/algorithm-universal233-ordinary-common-reduction-20261015T185752074314Z';A=R/'results/algorithm-universal233-ordinary-common-reduction-compressed-20261015T190441071133Z'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
c=json.loads((A/'certificate.json').read_text());assert c['status']=='PASS_AUTHOR_COMMON_REDUCTION_SOURCE_PRODUCER' and c['source_builds']==234 and c['stored_producer_occurrences']==5978
b=json.loads((B/'final-source-receipt-v1.json').read_text());assert b['fresh_modules']==9 and b['source_modules']==234
for n in ['CommonDispatch','CommonControls','CommonFalseControls']:assert sha(D/(n+'.lean'))==sha(B/(n+'.lean'))
files=sorted({p for base in [D,B,A] for p in base.rglob('*') if p.is_file()})
rows=[dict(path=str(p.relative_to(R)),sha256=sha(p)) for p in files]
rec=dict(version=1,utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),status='AUTHOR_SELECTED_COMMON_CHERRY_QUERY_EXACTNESS',no_further_writes=True,all_main_milestones='OPEN',novelty='OPEN',independent_acceptance=False,imported_source_modules=234,new_source_builds=9,unchanged_completed_source_and_binary_modules=225,stored_producer_occurrences=5978,axiom_union=c['axiom_union'],full_ordinary_solver=False,source_bit_payload_runtime='OPEN',runtime_ghost=False,canonical_build=str(B.relative_to(R)),canonical_audit=str(A.relative_to(R)),immutable_files=rows)
m=O/'COMMON-REDUCTION-MANIFEST-v1.json';m.write_text(json.dumps(rec,indent=2)+'\n')
for p in files+[m]:p.chmod(0o444)
for e in rows:assert sha(R/e['path'])==e['sha256']
print(json.dumps(dict(manifest=str(m.relative_to(R)),sha256=sha(m),members=len(rows))))
