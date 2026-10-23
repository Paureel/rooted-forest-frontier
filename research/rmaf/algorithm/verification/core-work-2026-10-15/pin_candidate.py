from pathlib import Path
import hashlib,json,shutil,datetime
root=Path(__file__).resolve().parents[5]
base=Path(__file__).resolve().parent
sha=lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
m=root/'research/rmaf/algorithm/universal233/core_work/CORE-WORK-MANIFEST-v1.json'
assert sha(m)=='5d878d6ff48fc62c5b4d72534b2900580e8154fd85be6aa8203380994a4d02ee'
data=json.loads(m.read_text()); checked=[]
for e in data['immutable_files']:
 p=root/e['path']; assert p.stat().st_size==e['bytes']; assert sha(p)==e['sha256'],str(p);checked.append(e)
r=base/'READY-ARTIFACTS.json';assert sha(r)=='bb49c561b6947acb600fb254b6349645e1035cb638fc2805fa320f8af88aa6b8'
for p,h in json.loads(r.read_text())['file_hashes'].items(): assert sha(root/p)==h,p
old=root/'research/rmaf/algorithm/verification/integration-2026-10-15/ARTIFACTS.json'
assert sha(old)=='4cbbba186a546ac48e5f27736b7a537a5d83d3b0bec40a2156b15d80040b1c65'
shutil.copyfile(m,base/'AUTHOR-MANIFEST.json')
isolated=base/'isolated';isolated.mkdir(exist_ok=True)
modules=['RMAF','CoreGraph','CoreProgram','CoreInvariants','CherryCoarsening','Geometry','Bridge','Composition','SourceBridge','Contraction','Normalization','InitialLift','Suppression','EraseLift','Origins','Branches','Payload','Primitive','Work','Controls']
prefix='results/algorithm-universal233-core-work-20261015T081612Z/'
selected=[]
for n in modules+['FalseAppend','FalseOracle','FalsePruned','FalseControl','TrueControl']:
 rel=prefix+n+'.lean';e=next(e for e in checked if e['path']==rel);shutil.copyfile(root/rel,isolated/(n+'.lean'));selected.append(e)
tool=next(e for e in checked if e['path'].endswith('/core_work/lean-toolchain'))
shutil.copyfile(root/tool['path'],isolated/'lean-toolchain')
receipt={'created_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'manifest_sha256':sha(m),'verified_author_entries':len(checked),'verified_readiness_entries':len(json.loads(r.read_text())['file_hashes']),'old_integration_manifest_identity_only':sha(old),'canonical_receipt':data['canonical_receipt'],'positive_modules':modules,'isolated_source_origins':selected,'source_only_no_oleans_copied':True}
(base/'CANDIDATE-PIN.json').write_text(json.dumps(receipt,indent=2)+'\n')
print(json.dumps({'verified_author_entries':len(checked),'verified_readiness_entries':receipt['verified_readiness_entries'],'isolated_sources':len(selected),'canonical_receipt':data['canonical_receipt']}))
