from pathlib import Path
import json,hashlib,datetime
root=Path(__file__).resolve().parents[5];b=Path(__file__).resolve().parent
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
a=b/'AUTHOR-MANIFEST.json';assert sha(a)=='5d878d6ff48fc62c5b4d72534b2900580e8154fd85be6aa8203380994a4d02ee'
author=json.loads(a.read_text())
for e in author['immutable_files']:
 p=root/e['path'];assert p.stat().st_size==e['bytes'] and sha(p)==e['sha256'],str(p)
ready=b/'READY-ARTIFACTS.json';assert sha(ready)=='bb49c561b6947acb600fb254b6349645e1035cb638fc2805fa320f8af88aa6b8'
for p,h in json.loads(ready.read_text())['file_hashes'].items():assert sha(root/p)==h,p
for e in json.loads((b/'CANDIDATE-PIN.json').read_text())['isolated_source_origins']:
 p=b/'isolated'/Path(e['path']).name;assert sha(p)==e['sha256'],str(p)
old=root/'research/rmaf/algorithm/verification/integration-2026-10-15/ARTIFACTS.json';assert sha(old)=='4cbbba186a546ac48e5f27736b7a537a5d83d3b0bec40a2156b15d80040b1c65'
receipt=json.loads((b/'FINAL-RECEIPT.json').read_text());assert receipt['main_milestones']==['OPEN']*3
assert receipt['complete_origin_inventory']['total']==1718 and receipt['candidate_literal_comparisons']==29
assert 'or measured machine-bound claim' not in (b/'FINAL-RECEIPT.json').read_text()
paths=[p for p in b.rglob('*') if p.is_file() and '__pycache__' not in p.parts and p.name!='ARTIFACTS.json']
paths += [p for p in (root/'research/rmaf/results').glob('algorithm-core-work-fresh-review-*') if p.is_file()]
paths=sorted(set(paths));files={str(p.relative_to(root)):{'sha256':sha(p),'bytes':p.stat().st_size} for p in paths}
result={'status':'FROZEN-SCOPED-REVIEW-WITH-SOURCE-UNIT-CORRECTION','created_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'author_manifest_sha256':sha(a),'author_entries_rechecked':len(author['immutable_files']),'readiness_entries_rechecked':len(json.loads(ready.read_text())['file_hashes']),'prior_integration_manifest_identity_only':sha(old),'file_count':len(files),'files':files,'excludes':['this manifest itself','Python caches'],'all_three_main_milestones':'OPEN','independent_replications_added':0}
p=b/'ARTIFACTS.json';p.write_text(json.dumps(result,indent=2)+'\n');print(json.dumps({'file_count':len(files),'manifest_sha256':sha(p),'author_entries_rechecked':result['author_entries_rechecked'],'readiness_entries_rechecked':result['readiness_entries_rechecked'],'status':result['status']}))
