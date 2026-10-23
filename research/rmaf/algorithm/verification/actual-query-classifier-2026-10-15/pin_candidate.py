from pathlib import Path
import json,hashlib,shutil,datetime
b=Path(__file__).resolve().parent
root=b.parents[4]
h=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
pins={
 'query':('research/rmaf/algorithm/universal233/query_scheduler/QUERY-SCHEDULER-MANIFEST-v1.json','3e91794e8e5a15d979e11dc17cd8087d294fee8e1dbe5cc627249e6c5d24e68e',54,'results/algorithm-universal233-query-20261015T101316Z/'),
 'rank':('research/rmaf/algorithm/universal233/rank_consumer/RANK-CONSUMER-MANIFEST-v1.json','b429f361f6ce0ce11dd641e7bbc545eb0fda3411d2ebfef5e748419bfb0691a0',153,'results/algorithm-universal233-rank-consumer-20261015T094545Z/')}
out={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'source_only':True,'lineage':'same independent reviewer and prior ledger; zero extra replications','packages':{}}
for label,(path,sha,n,prefix) in pins.items():
 p=root/path;assert h(p)==sha
 d=json.loads(p.read_text());assert len(d['immutable_files'])==n
 for x in d['immutable_files']:assert h(root/x['path'])==x['sha256'],x
 shutil.copyfile(p,b/('AUTHOR-'+label.upper()+'-MANIFEST.json'))
 iso=b/('isolated-'+label);iso.mkdir(exist_ok=True)
 copied=[]
 for x in d['immutable_files']:
  p=Path(x['path'])
  if x['path'].startswith(prefix) and p.suffix=='.lean' and p.stem not in ['ModuleAudit','PlantAudit','PlantPrivate','TrueControl']:
   dst=iso/p.name;shutil.copyfile(root/p,dst);copied.append({'module':p.stem,'origin_path':str(p),'sha256':h(dst)})
 (iso/'lean-toolchain').write_text('leanprover/lean4:v4.35.0\n')
 out['packages'][label]={'manifest_sha256':sha,'entries_matched':n,'copied_sources':copied,'canonical_receipt':prefix+'certificate.json'}
ready=b/'READY-ARTIFACTS.json';assert h(ready)=='655f32eef6ee281e4d820e49e26d2b20bbf694f11e27cb0605ca4c5d2ac5f535'
rd=json.loads(ready.read_text());assert len(rd['file_hashes'])==60
for p,sha in rd['file_hashes'].items():assert h(root/p)==sha,p
out['readiness']={'manifest_sha256':h(ready),'entries_matched':60}
old=root/'research/rmaf/algorithm/verification/whole-source-work-2026-10-15/ARTIFACTS.json'
assert h(old)=='2526f8cb77fad799770557765a9d862d54e84fd31a0c1d49e20afd4254741580'
out['previous_whole_review_manifest_sha256']=h(old)
(b/'CANDIDATE-PIN.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({k:{'entries':v['entries_matched'],'sources':len(v['copied_sources'])} for k,v in out['packages'].items()}))
