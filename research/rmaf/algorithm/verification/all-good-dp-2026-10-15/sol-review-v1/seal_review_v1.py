"""One-shot immutable review snapshot; never overwrites an existing seal."""
from pathlib import Path
from hashlib import sha256
from datetime import datetime,timezone
import json,shutil
H=Path(__file__).resolve().parent;DEST=H.parent/'sol-frozen-review-v1';assert not DEST.exists(),'Refuse to overwrite an existing frozen report'
v=json.loads((H/'VERDICT-v1.json').read_text());p=json.loads((H/'FINAL-PRESERVATION-v1.json').read_text());assert p['status']=='FINAL-PRESERVATION-PASS' and p['pinnedEntriesMatched']==980
assert v['grade']=='SCOPED_PASS_WITH_COST_DOCUMENTATION_FINDING' and not v['verifiedClosed'] and not v['candidateSourcesEdited']
for name,key,want in [('native-fixed-v2.json','status','NATIVE-COMPARISONS-PASS'),('native-geometry-v1.json','status','NATIVE-ORIGINAL-GEOMETRY-PASS'),('STORED-AUDIT-SUMMARY-v4.json','status','STORED-PRODUCER-AUDIT-PASS'),('GENERATED-BODIES-v1.json','status','ACTUAL-GENERATED-BODIES-PASS'),('COMPILER-EXTRA-AUDIT-v1.json','status','COMPILER-EXTRA-ORIGIN-METADATA-PASS'),('AUDIT-AND-RUNTIME-SUMMARY-v1.json','status','PRODUCER-RESOLVED-AND-VALUE-CLOSURE-PASS')]:assert json.loads((H/name).read_text())[key]==want
DEST.mkdir()
for source in sorted(H.rglob('*')):
 if not source.is_file() or '__pycache__' in source.parts or source.suffix=='.pyc':continue
 target=DEST/source.relative_to(H);target.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(source,target)
files=[{'path':f.relative_to(DEST).as_posix(),'bytes':f.stat().st_size,'sha256':sha256(f.read_bytes()).hexdigest()} for f in sorted(DEST.rglob('*')) if f.is_file()]
x={'status':v['grade'],'sealUTC':datetime.now(timezone.utc).isoformat(),'artifactCount':len(files),'files':files,'verdict':v,'preservation':p,'scope':'Exact66-source released consumer closure; original157 READY preserved; fresh stored-producer detector separately versioned before candidate source contact.','report':'REVIEW-REPORT-v1.md','costFinding':'COST-REVIEW-v1.md','freshContextProseRefereeCredit':False,'allThreeMainMilestones':'OPEN','novelty':'OPEN','verifiedClosed':False}
mp=DEST/'REVIEW-MANIFEST-v1.json';mp.write_text(json.dumps(x,indent=2)+'\n');pin=sha256(mp.read_bytes()).hexdigest();(DEST/'REVIEW-MANIFEST-v1.sha256').write_text(pin+'  REVIEW-MANIFEST-v1.json\n')
for e in files:
 f=DEST/e['path'];assert f.stat().st_size==e['bytes'] and sha256(f.read_bytes()).hexdigest()==e['sha256']
for f in DEST.rglob('*'):
 if f.is_file():f.chmod(0o444)
for d in sorted([d for d in DEST.rglob('*') if d.is_dir()],key=lambda d:len(d.parts),reverse=True):d.chmod(0o555)
DEST.chmod(0o555)
print(json.dumps({'status':x['status'],'manifest':str(mp),'sha256':pin,'artifacts':len(files),'allThreeMainMilestones':'OPEN','verifiedClosed':False}))
