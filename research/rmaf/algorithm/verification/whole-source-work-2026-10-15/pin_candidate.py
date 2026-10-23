from pathlib import Path
import json,hashlib,shutil,datetime,re
root=Path(__file__).resolve().parents[5];b=Path(__file__).resolve().parent
h=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
p=root/'research/rmaf/algorithm/universal233/whole_source_work/WHOLE-SOURCE-WORK-MANIFEST-v1.json';assert h(p)=='d0e00ddaf7ac3d30e47e84cded68b8c47348e33f8f7da74778353fccd618063b'
x=json.loads(p.read_text())
for e in x['immutable_files']:
 q=root/e['path'];assert q.stat().st_size==e['bytes'] and h(q)==e['sha256'],str(q)
r=b/'READY-ARTIFACTS.json';assert h(r)=='174bb34de5160c5c0923d8466d27becf855a7c495030845853edf4250df6ea71'
for q,s in json.loads(r.read_text())['file_hashes'].items():assert h(root/q)==s,q
old={}
for name,want in [('core-work-2026-10-15','61e9aaa274f9ac625939efc3315bf9aa93638435daa90ae039d41a5ebbc67455'),('integration-2026-10-15','4cbbba186a546ac48e5f27736b7a537a5d83d3b0bec40a2156b15d80040b1c65')]:
 q=b.parent/name/'ARTIFACTS.json';assert h(q)==want;old[name]=h(q)
shutil.copyfile(p,b/'AUTHOR-MANIFEST.json');iso=b/'isolated';iso.mkdir(exist_ok=True)
prefix='results/algorithm-universal233-whole-work-20261015T084849Z/';excluded={'ModuleInventory','ModulePlantAudit','PlantModel'};negative={'FalseAppend','FalseColorCount','FalsePruned','FalseControl','TrueControl'};origins=[]
for e in x['immutable_files']:
 q=Path(e['path'])
 if e['path'].startswith(prefix) and q.suffix=='.lean' and q.stem not in excluded:
  shutil.copyfile(root/q,iso/q.name);origins.append(e)
mods=sorted(Path(e['path']).stem for e in origins if Path(e['path']).stem not in negative)
assert len(mods)==37
order=[];pending=set(mods)
while pending:
 ready=[m for m in sorted(pending) if not(set(re.findall(r'^import\s+(\w+)',(iso/(m+'.lean')).read_text(),re.M))&pending)]
 assert ready,pending
 for m in ready:order.append(m);pending.remove(m)
tool=next(e for e in x['immutable_files'] if e['path'].endswith('/whole_source_work/lean-toolchain'));shutil.copyfile(root/tool['path'],iso/'lean-toolchain')
receipt={'created_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'manifest_sha256':h(p),'author_entries_verified':len(x['immutable_files']),'readiness_entries_verified':len(json.loads(r.read_text())['file_hashes']),'old_manifest_identities_only':old,'positive_modules':mods,'topological_rebuild_order':order,'isolated_source_origins':origins,'author_audit_and_plant_implementations_not_copied':sorted(excluded),'no_oleans_copied':True,'canonical_receipt':x['canonical_receipt']}
(b/'CANDIDATE-PIN.json').write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps({k:receipt[k] for k in ['author_entries_verified','readiness_entries_verified','positive_modules','topological_rebuild_order']}))
