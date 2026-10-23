"""One-shot immutable author release. Preserve all predecessor evidence."""
from pathlib import Path
import datetime,hashlib,json,shutil
D=Path(__file__).resolve().parent;R=D.parents[5];O=D/'local_ih_release_v1';P=D.parent/'forest_local_ih'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
for n in ['LocalCongruence','LocalExact','LocalControls','TransferControls','FalseDiscount','FalseUnboundedTransfer']:
 shutil.copyfile(P/(n+'.lean'),O/(n+'.lean'))
B=R/'results/algorithm-universal233-forest-local-ih-replay-v2-20261015T182229550641Z';A=R/'results/algorithm-universal233-forest-local-ih-compressed-20261015T183036528254Z';F=R/'results/algorithm-universal233-forest-local-ih-replay-20261015T181403409989Z'
c=json.loads((A/'certificate.json').read_text());assert c['status']=='PASS_AUTHOR_LOCAL_IH_TRANSFER_SOURCE_PRODUCER' and c['source_builds']==92 and c['stored_producer_occurrences']==3443
for n in ['LocalCongruence','LocalExact','LocalControls','TransferControls']:assert sha(O/(n+'.lean'))==sha(B/(n+'.lean'))
(O/'FRESH-CONTROLS-SNAPSHOT.json').write_text(json.dumps(dict(origin=c['fresh_controls_receipt'],controls=c['controls'],qualification='Historical origin hash is not a final immutable-file pin; control records embedded here.'),indent=2)+'\n')
files=list(O.rglob('*'))+list(B.rglob('*'))+list(A.rglob('*'))+list(F.rglob('*'))
for n in ['replay_local_ih.py','replay_local_ih_v2.py','audit_local_ih_compressed.py','compressed_pool_resume_v3.py','AUDIT-PLAN-v1.md','COMPRESSED-AUDIT-AMENDMENT-v1.md','PROOF-TEXT-SCOPE-v3.md']:files.append(D/n)
files=sorted({p for p in files if p.is_file()})
rows=[dict(path=str(p.relative_to(R)),sha256=sha(p)) for p in files]
rec=dict(version=1,utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),status='AUTHOR_SOURCE_PRODUCER_BUDGET_LOCAL_EXACTNESS',no_further_writes=True,all_main_milestones='OPEN',novelty='OPEN',independent_acceptance=False,source_builds=92,stored_producer_occurrences=3443,axiom_union=c['axiom_union'],runtime_ghost=False,full_ordinary_solver=False,source_work_claim=False,compiled_runtime_claim=False,canonical_source_replay=str(B.relative_to(R)),canonical_producer_audit=str(A.relative_to(R)),producer_proof_text_scope='Theorem proof text omitted only; actual proof references traversed. Nonproof opaque/data values fully recorded; full proof olean pinned.',immutable_files=rows,external_manifest_pins=[dict(path='research/rmaf/algorithm/universal233/forest_solver/FOREST-SOLVER-MANIFEST-v3.json',sha256='89937a6f71bceb2dbeb64917b4b805e8f193fa485b00ec28acecdc95d047dcf5'),dict(path='research/rmaf/algorithm/ordinary_dispatch/forest_min_completion/FOREST-MIN-COMPLETION-MANIFEST-v1.json',sha256='0be74cd7bfc28cfaa382ea0610472bea7d64e601a7cab5919727ee993ca2cef4')])
m=O/'LOCAL-IH-MANIFEST-v1.json';m.write_text(json.dumps(rec,indent=2)+'\n')
for p in files+[m]:p.chmod(0o444)
for e in rows:assert sha(R/e['path'])==e['sha256']
print(json.dumps(dict(manifest=str(m.relative_to(R)),sha256=sha(m),members=len(rows))))
