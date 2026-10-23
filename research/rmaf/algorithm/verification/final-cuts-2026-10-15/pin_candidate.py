from pathlib import Path
import json,hashlib,shutil,datetime
b=Path(__file__).resolve().parent;root=b.parents[4];h=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
source=root/'research/rmaf/algorithm/universal233/final_cut_recovery/FINAL-CUTS-MANIFEST-v1.json';sha='95569c46912bff25f74cd01174bc51a934e7395524922271e6de4538fbdc4fb3';assert h(source)==sha;d=json.loads(source.read_text());assert len(d['immutable_files'])==618
for x in d['immutable_files']:assert h(root/x['path'])==x['sha256'],x
shutil.copyfile(source,b/'AUTHOR-MANIFEST.json');iso=b/'isolated';iso.mkdir(exist_ok=True);copies=[]
exclude=['ModuleAudit','PlantAudit','PlantForeign','SourcePinPlant','TrueControl'];negative=['FalseControl','FalseControls'];prefix='results/algorithm-universal233-final-cuts-replay-20261015T105812Z/'
for x in d['immutable_files']:
 p=Path(x['path'])
 if x['path'].startswith(prefix) and p.suffix=='.lean' and p.stem not in exclude:
  shutil.copyfile(root/p,iso/p.name);copies.append({'module':p.stem,'source_path':x['path'],'sha256':x['sha256'],'positive':p.stem not in negative+['Interfaces'],'role':'author-interface-printing-not-executed' if p.stem=='Interfaces' else 'explicit-false' if p.stem in negative else 'scientific-positive'})
(iso/'lean-toolchain').write_text('leanprover/lean4:v4.35.0\n')
ready=b/'READY-ARTIFACTS.json';assert h(ready)=='b5ddb36b1b49641d9780c97442c8d1669f8aad2500ae961e6a182b1ef6ba47fe';rd=json.loads(ready.read_text());assert len(rd['file_hashes'])==55
for path,sh in rd['file_hashes'].items():assert h(root/path)==sh,path
old=b.parent/'actual-query-classifier-2026-10-15/ARTIFACTS.json';assert h(old)=='b7c7fa96d1ea95f91d41218e537b098ce15d5a9cee87375ec212a7f54837cdd8'
out={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'author_manifest_sha256':sha,'author_entries_matched':618,'readiness_entries_matched':55,'readiness_manifest_sha256':h(ready),'previous275_manifest_sha256':h(old),'copied_sources':copies,'positive_modules':sum(x['positive'] for x in copies),'canonical_receipt':prefix+'certificate.json','bound_result':'results/algorithm-universal233-final-cuts-20261015T105907Z.json','source_only':True,'copied_scientific_oleans':0,'extra_replications':0};(b/'CANDIDATE-PIN.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps({k:v for k,v in out.items() if k!='copied_sources'}))
