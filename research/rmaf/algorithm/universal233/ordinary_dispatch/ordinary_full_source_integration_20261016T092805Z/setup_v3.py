# Exact sealed consumer union; object differences require producer compatibility.
from pathlib import Path
import datetime,hashlib,json,os,re,shutil
D=Path(__file__).resolve().parent;R=D.parents[5]
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
T=R/'research/rmaf/monitoring/global-next-20261016T092805Z/GLOBAL-INTEGRATION-TARGET-v1.json'
assert sha(T)=='0b64f4c7cb866f1927f96bf9a0847bf99bf0e981e5f2edeee1b3dabf5158eb23'
t=json.loads(T.read_text());ms={}
for k in ['weighted_prefix_common_agreement','selected_rule5_forest_arms']:
 e=t['allowed_packages'][k];p=R/e['manifest'];assert sha(p)==e['sha256'];ms[k]=json.loads(p.read_text())
 for f in ms[k]['immutable_files']:
  assert sha(R/f['path'])==f['sha256'],f['path']
P=R/ms['weighted_prefix_common_agreement']['canonical_build'];S=R/ms['selected_rule5_forest_arms']['canonical_build'];pool=R/ms['selected_rule5_forest_arms']['dependency_pool']
dep_entries=json.loads((R/ms['selected_rule5_forest_arms']['dependency_provenance']).read_text())['entries']
assert shutil.disk_usage(R).free>=3*(1<<30)
B=R/'results'/('algorithm-universal233-source-integration-20261016T092805Z-'+datetime.datetime.now(datetime.timezone.utc).strftime('%Y%m%dT%H%M%S%fZ'));B.mkdir()
rec=dict(status='CHECKING',target_sha256=sha(T),inputs={k:t['allowed_packages'][k] for k in ms},sources=[],object_identity_differences=[],source_conflicts=[],independent_acceptance=False,all_main_milestones='OPEN',primitive_bits='OPEN')
def save():(B/'SEED.json').write_text(json.dumps(rec,indent=2)+'\n')
save();seen={};visited=set()
def add(n,root,fallback,package):
 p=root/(n+'.lean');o=root/(n+'.olean')
 if root==pool:
  e=dep_entries[n];p=R/e['source'];o=R/e['loaded_olean'];assert sha(p)==e['source_sha256'] and sha(o)==e['loaded_sha256']
 assert p.exists() and o.exists(),(n,root)
 key=(n,str(root))
 if key in visited:return
 visited.add(key)
 for dep in re.findall(r'^import ([A-Za-z0-9_\'.]+)\s*$',p.read_text(),re.M):
  if dep.split('.')[0] not in {'Init','Std','Lean'}:
   add(dep,root if (root/(dep+'.lean')).exists() else fallback,fallback,package)
 e=dict(module=n,package=package,source=str(p.relative_to(R)),source_sha256=sha(p),olean=str(o.relative_to(R)),olean_sha256=sha(o))
 if n in seen:
  old=seen[n];assert e['source_sha256']==old['source_sha256'],('SOURCE_CONFLICT',n)
  if e['olean_sha256']!=old['olean_sha256']:rec['object_identity_differences'].append(dict(module=n,chosen=old,alternative=e))
  return
 for src in [p,o]:
  assert not src.stat().st_mode&0o222,('UNSEALED_SOURCE',str(src))
  os.link(src,B/src.name)
 seen[n]=e;rec['sources'].append(e)
for p in sorted(P.glob('*.lean')):
 if (P/(p.stem+'.olean')).exists():add(p.stem,P,P,'weighted_prefix_common_agreement')
add('ForestArmBinding',S,pool,'selected_rule5_forest_arms')
shutil.copyfile(P/'lean-toolchain',B/'lean-toolchain')
rec['status']='PASS_EXACT_LICENSED_CONSUMER_SEED_COMPATIBILITY_AUDIT_PENDING';save()
(D/'BUILD-v1.json').write_text(json.dumps(dict(directory=str(B.relative_to(R)),seed_sha256=sha(B/'SEED.json')),indent=2)+'\n')
print(rec['status'],'modules',len(seen),'object_differences',len(rec['object_identity_differences']))
