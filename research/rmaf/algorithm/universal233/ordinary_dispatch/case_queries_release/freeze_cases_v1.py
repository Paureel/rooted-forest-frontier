# One-shot immutable seal; all actual scientific checks ran separately first.
from pathlib import Path
import datetime,hashlib,json
D=Path(__file__).resolve().parent;R=D.parents[5]
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
configs=[('disjoint_parent_query',7,285,169),('pair_allgood_query',6,269,153)];roots=[D];components=[]
for name,new,modules,stored in configs:
 W=D.parent/name;B=R/json.loads((W/'LATEST-BUILD-v1.json').read_text())['directory'];A=R/json.loads((W/'LATEST-AUDIT-v1.json').read_text())['directory'];c=json.loads((A/'certificate.json').read_text());assert c['status']=='PASS_AUTHOR_ACTUAL_CASE_QUERY_SOURCE_PRODUCER' and c['new_builds']==new and c['imported_modules']==modules and c['new_stored_occurrences']==stored
 for p,h in json.loads((A/'BUILD-PINS.json').read_text()).items():assert sha(R/p)==h
 for p,h in c['inputs'].items():assert sha(R/p)==h
 roots += [W,B,A];components.append(dict(name=name,canonical_build=str(B.relative_to(R)),canonical_audit=str(A.relative_to(R)),certificate_sha256=sha(A/'certificate.json'),new_source_builds=new,actual_imported_modules=modules,new_stored_occurrences=stored,axiom_union=c['axiom_union'],interfaces=c['interfaces']))
roots.append(R/'results/algorithm-universal233-disjoint-parent-query-audit-20261015T201545860250Z')
files=sorted({p for root in roots for p in root.rglob('*') if p.is_file()});rows=[dict(path=str(p.relative_to(R)),sha256=sha(p)) for p in files]
m=D/'CASE-QUERIES-MANIFEST-v1.json';assert not m.exists();rec=dict(version=1,utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),status='AUTHOR_ACTUAL_ORIGINAL_PARENT_CASE_QUERY_EXACTNESS',no_further_writes=True,all_main_milestones='OPEN',novelty='OPEN',source_bit_payload_runtime='OPEN',full_faster_solver=False,independent_acceptance=False,runtime_ghost=False,components=components,immutable_files=rows);m.write_text(json.dumps(rec,indent=2)+'\n')
for p in files+[m]:p.chmod(0o444)
for e in rows:assert sha(R/e['path'])==e['sha256']
print(json.dumps(dict(manifest=str(m.relative_to(R)),sha256=sha(m),members=len(rows))))
