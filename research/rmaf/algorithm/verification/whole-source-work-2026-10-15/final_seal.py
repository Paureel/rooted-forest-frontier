from pathlib import Path
import json,hashlib,datetime
root=Path(__file__).resolve().parents[5];b=Path(__file__).resolve().parent;h=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
a=b/'AUTHOR-MANIFEST.json';assert h(a)=='d0e00ddaf7ac3d30e47e84cded68b8c47348e33f8f7da74778353fccd618063b';author=json.loads(a.read_text())
for e in author['immutable_files']:
 p=root/e['path'];assert p.stat().st_size==e['bytes'] and h(p)==e['sha256'],str(p)
r=b/'READY-ARTIFACTS.json';assert h(r)=='174bb34de5160c5c0923d8466d27becf855a7c495030845853edf4250df6ea71'
for p,s in json.loads(r.read_text())['file_hashes'].items():assert h(root/p)==s,p
for e in json.loads((b/'CANDIDATE-PIN.json').read_text())['isolated_source_origins']:
 p=b/'isolated'/Path(e['path']).name;assert h(p)==e['sha256'],str(p)
old={}
for name,want in [('core-work-2026-10-15','61e9aaa274f9ac625939efc3315bf9aa93638435daa90ae039d41a5ebbc67455'),('integration-2026-10-15','4cbbba186a546ac48e5f27736b7a537a5d83d3b0bec40a2156b15d80040b1c65')]:
 p=b.parent/name/'ARTIFACTS.json';assert h(p)==want;old[name]=h(p)
x=json.loads((b/'FINAL-RECEIPT.json').read_text());assert x['main_milestones']==['OPEN']*3 and x['origin_inventory']['total']==2565 and x['compiled_value_relations']==43 and x['adapter_v1_v2_expectations_equal']
paths=[p for p in b.rglob('*') if p.is_file() and '__pycache__' not in p.parts and p.name!='ARTIFACTS.json'];paths+=[p for p in (root/'research/rmaf/results').glob('algorithm-whole-source-work-fresh-review-*') if p.is_file()];paths=sorted(set(paths))
files={str(p.relative_to(root)):{'sha256':h(p),'bytes':p.stat().st_size} for p in paths}
result={'status':'FROZEN-SCOPED-WHOLE-SOURCE-WORK-REVIEW','created_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'author_manifest_sha256':h(a),'author_entries_rechecked':len(author['immutable_files']),'readiness_entries_rechecked':len(json.loads(r.read_text())['file_hashes']),'prior_manifest_identities_only':old,'file_count':len(files),'files':files,'excludes':['this manifest itself','Python caches'],'independent_replications_added':0,'all_three_main_milestones':'OPEN','selector_gate_dispatch':'OPEN','source_operation_unit_correction':'explicit64-helper/8-cell contracts;no extracted operational theorem'}
p=b/'ARTIFACTS.json';p.write_text(json.dumps(result,indent=2)+'\n')
for k,e in files.items():assert h(root/k)==e['sha256'] and (root/k).stat().st_size==e['bytes'],k
print(json.dumps({'file_count':len(files),'manifest_sha256':h(p),'author_entries_rechecked':result['author_entries_rechecked'],'readiness_entries_rechecked':result['readiness_entries_rechecked'],'status':result['status']}))
