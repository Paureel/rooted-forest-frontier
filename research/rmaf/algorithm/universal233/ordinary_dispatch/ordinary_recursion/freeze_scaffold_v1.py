from pathlib import Path
import datetime,hashlib,json
D=Path(__file__).resolve().parent;R=D.parents[5];B=R/'results/algorithm-universal233-ordinary-recursion-20261015T191007632025Z';F=R/'results/algorithm-universal233-ordinary-recursion-20261015T190959286006Z';O=D/'release_v1';A=R/json.loads((D/'LATEST-AUDIT-v1.json').read_text())['directory']
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
c=json.loads((A/'certificate.json').read_text());assert c['status']=='PASS_AUTHOR_COMPLETE_CHERRY_SCAFFOLD_SOURCE_PRODUCER' and c['new_builds']==5 and c['new_stored_occurrences']==315 and c['imported_modules']==252 and c['total_selected_stored_occurrences']==6370
for n in ['OrdinaryScaffold','ScaffoldFacts','ScaffoldExact','ScaffoldControlPilot','ScaffoldControls','ScaffoldFalseControls']:assert sha(D/(n+'.lean'))==sha(B/(n+'.lean'))
files={p for base in [D,B,A] for p in base.rglob('*') if p.is_file()}
# Preserve every failed staging root actually produced by these runners.
for q in (R/'results').glob('algorithm-universal233-ordinary-recursion-*'):
 if q==B:continue
 cert=q/'certificate.json'
 if cert.exists() and json.loads(cert.read_text()).get('status')=='FAILED_NOT_ACCEPTED':files.update(p for p in q.rglob('*') if p.is_file())
files=sorted(files);rows=[dict(path=str(p.relative_to(R)),sha256=sha(p)) for p in files]
rec=dict(version=1,utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),status='AUTHOR_COMPLETE_EXACT_ORDINARY_CHERRY_SCAFFOLD',no_further_writes=True,independent_acceptance=False,intended_faster_algorithm='OPEN',intended_integrated_correctness='OPEN',smaller_base='OPEN',novelty='OPEN',scaffold_semantics='Every proper ordinary pair and every cut budget; global component minimum or exact bounded negative.',new_builds=5,immutable_dependency_modules=247,new_stored_occurrences=315,total_selected_stored_occurrences=6370,axiom_union=c['axiom_union'],canonical_build=str(B.relative_to(R)),canonical_audit=str(A.relative_to(R)),source_bit_payload_runtime='OPEN',base233_claim=False,runtime_ghost=False,reference_absence_scope='Conservative local full-reference closure; external Std/Lean/Init bodies not inspected.',immutable_files=rows)
m=O/'SCAFFOLD-MANIFEST-v1.json';m.write_text(json.dumps(rec,indent=2)+'\n')
for p in files+[m]:p.chmod(0o444)
for e in rows:assert sha(R/e['path'])==e['sha256']
print(json.dumps(dict(manifest=str(m.relative_to(R)),sha256=sha(m),members=len(rows))))
