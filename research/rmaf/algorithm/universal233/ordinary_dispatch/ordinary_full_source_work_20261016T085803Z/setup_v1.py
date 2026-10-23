# One-shot licensed consumer union. Different object identities are recorded;
# exact nonproof producer compatibility remains a required audit before sealing.
from pathlib import Path
import datetime,hashlib,json,os,re,shutil
D=Path(__file__).resolve().parent;R=D.parents[5]
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
T=R/'research/rmaf/monitoring/global-next-20261016T085803Z/GLOBAL-SOURCE-TARGET-v2.json'
assert sha(T)=='1b20034e34b9e6902572af6273abdcccf121dd09f6257362e88b2c8c9a160db9'
t=json.loads(T.read_text());manifests={}
for k in ['call_count','early','rule5_classifier','rule5common']:
 e=t['allowed_packages'][k];p=R/e['manifest'];assert sha(p)==e['sha256'];manifests[k]=json.loads(p.read_text())
P=R/manifests['call_count']['canonical_build'];E=R/manifests['early']['canonical_receipt'];C=R/manifests['rule5_classifier']['canonical_build'];M=R/manifests['rule5common']['canonical_receipt']['receipt']
assert shutil.disk_usage(R).free>=3*(1<<30)
B=R/'results'/('algorithm-universal233-full-source-20261016T085803Z-'+datetime.datetime.now(datetime.timezone.utc).strftime('%Y%m%dT%H%M%S%fZ'));B.mkdir()
rec=dict(status='CHECKING',target_sha256=sha(T),inputs=t['allowed_packages'],sources=[],object_identity_differences=[],source_conflicts=[],independent_acceptance=False,all_main_milestones='OPEN',primitive_bits='OPEN')
def save():(B/'SEED.json').write_text(json.dumps(rec,indent=2)+'\n')
save();seen={}
def add(n,root,package):
 p=root/(n+'.lean');o=root/(n+'.olean');assert p.exists() and o.exists(),n
 if n in seen:
  old=seen[n];assert sha(p)==old['source_sha256'],('SOURCE_CONFLICT',n)
  if sha(o)!=old['olean_sha256']:
   rec['object_identity_differences'].append(dict(module=n,chosen=old,alternative=dict(package=package,source=str(p.relative_to(R)),source_sha256=sha(p),olean=str(o.relative_to(R)),olean_sha256=sha(o))))
  return
 for dep in re.findall(r'^import ([A-Za-z0-9_\'.]+)\s*$',p.read_text(),re.M):
  if dep.split('.')[0] not in {'Init','Std','Lean'}:
   depRoot=root if (root/(dep+'.lean')).exists() else P
   add(dep,depRoot,package)
 for src in [p,o]:
  assert not src.stat().st_mode&0o222,('UNSEALED_SOURCE',str(src))
  os.link(src,B/src.name)
 e=dict(module=n,package=package,source=str(p.relative_to(R)),source_sha256=sha(p),olean=str(o.relative_to(R)),olean_sha256=sha(o));seen[n]=e;rec['sources'].append(e)
for n in ['OrdinaryCallControls','ForestNatSplit']:add(n,P,'call_count')
for n,root,k in [('ERInterface',E,'early'),('ClassifierPayload',C,'rule5_classifier'),('CommonLocalBinding',M,'rule5common')]:add(n,root,k)
shutil.copyfile(P/'lean-toolchain',B/'lean-toolchain')
rec['status']='PASS_EXACT_LICENSED_CONSUMER_SEED_COMPATIBILITY_AUDIT_PENDING';save()
(D/'BUILD-v1.json').write_text(json.dumps(dict(directory=str(B.relative_to(R)),seed_sha256=sha(B/'SEED.json')),indent=2)+'\n')
print(rec['status'],'modules',len(seen),'object_differences',len(rec['object_identity_differences']))
