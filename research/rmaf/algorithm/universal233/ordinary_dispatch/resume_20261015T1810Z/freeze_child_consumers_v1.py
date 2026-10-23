from pathlib import Path
import datetime,hashlib,json,shutil
D=Path(__file__).resolve().parent;R=D.parents[5];O=D/'child_consumer_release_v1';B=R/'results/algorithm-universal233-ordinary-child-binding-20261015T182851721674Z';A=R/'results/algorithm-universal233-ordinary-child-consumer-compressed-20261015T185512557908Z'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
c=json.loads((A/'certificate.json').read_text());assert c['status']=='PASS_AUTHOR_ACTUAL_CHILD_CONSUMER_SOURCE_PRODUCER' and c['source_builds']==151 and c['stored_producer_occurrences']==4883
names=['ChildForestBinding','PaidChildren','CherryDispatch','Rule4Dispatch','ChildConsumerControls','ChildConsumerFalseControls']
for n in names:
 p=D/(n+'.lean');assert sha(p)==sha(B/p.name);shutil.copyfile(p,O/p.name)
initial=json.loads((B/'certificate.json').read_text());target='research/rmaf/algorithm/universal233/ordinary_dispatch/resume_20261015T1810Z/CHILD-CONSUMER-TARGET-v1.md';assert sha(D/'CHILD-CONSUMER-TARGET-before-controls-v1.md')==initial['inputs'][target]
files=list(O.rglob('*'))+list(B.rglob('*'))
for p in (R/'results').glob('algorithm-universal233-ordinary-child-consumer-compressed-*'):files+=list(p.rglob('*'))
for n in ['build_child_binding.py','extend_child_binding.py','audit_child_consumers_v1.py','audit_child_consumers_v2.py','build_paid_children_controls.py','build_paid_children_controls_v2.py','CHILD-COMPILE-CONTROLS-v1.json','CHILD-COMPILE-CONTROLS-v2.json','CHILD-CONSUMER-TARGET-v1.md','CHILD-CONSUMER-TARGET-before-controls-v1.md']+[p.name for p in D.glob('*-controls-v*.log')]+[p.name for p in D.glob('CherryDispatch-dev*')]+['PaidChildren-dev1.log','ChildConsumerControls-decide-failure-v1.lean.txt']:files.append(D/n)
files+=[D/(n+'.lean') for n in names];files=sorted({p for p in files if p.is_file()})
rows=[dict(path=str(p.relative_to(R)),sha256=sha(p)) for p in files]
rec=dict(version=1,utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),status='AUTHOR_ACTUAL_PAID_CHILD_CONSUMERS',no_further_writes=True,all_main_milestones='OPEN',novelty='OPEN',independent_acceptance=False,source_modules=151,stored_producer_occurrences=4883,axiom_union=c['axiom_union'],runtime_ghost=False,full_ordinary_solver=False,source_bit_payload_runtime='OPEN',canonical_build=str(B.relative_to(R)),canonical_audit=str(A.relative_to(R)),producer_scope=c['theorem_proof_text'],immutable_files=rows)
m=O/'CHILD-CONSUMER-MANIFEST-v1.json';m.write_text(json.dumps(rec,indent=2)+'\n')
for p in files+[m]:p.chmod(0o444)
for e in rows:assert sha(R/e['path'])==e['sha256']
print(json.dumps(dict(manifest=str(m.relative_to(R)),sha256=sha(m),members=len(rows))))
