from pathlib import Path
import json,hashlib,re,shutil
D=Path(__file__).resolve().parent;R=D.parents[5]
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
T=R/'research/rmaf/monitoring/rule5-next-20261016T105342Z/RULE5-CLOSED-SOURCE-TARGET-v1.json';assert sha(T)=='b29b5c6c9cf307de1ce5fe1cdeb7a2dd37a62a8cf7a89089ef6410bb47073f26';t=json.loads(T.read_text());ms={}
for k,e in t['allowed_packages'].items():
 p=R/e['manifest'];assert sha(p)==e['sha256'];ms[k]=json.loads(p.read_text())
P=R/'research/rmaf/algorithm/universal233/ordinary_dispatch/rule5_execution_source_20261016T100131Z';prev=json.loads((P/'DEPENDENCIES-v1.json').read_text());O=R/ms['rule5_execution']['canonical_build'];F=R/ms['classifier_fee']['canonical_build'];L=R/ms['literal_fee']['canonical_build'];H=R/ms['hard2_front']['canonical_build'];POOL=R/'research/rmaf/algorithm/universal233/ordinary_dispatch/rule5_selected_local_work_20261016T090023Z/imports';FC=R/'research/rmaf/algorithm/universal233/ordinary_dispatch/classifier_check_fee_20261016T103025Z/checker-imports'
paths=[O]+[R/p for p in prev['import_paths']]+[F,L,FC,H];entries={};bridges=[]
source_pool={}
for n,e in prev['entries'].items():source_pool[n]=(R/e['source'],R/e['loaded_olean'],'previous_exact_closure')
for key,path in [('rule5_execution',O),('classifier_fee',F),('literal_fee',L),('hard2_front',H)]:
 own=ms[key].get('own_modules',ms[key].get('own_proof_modules',[]))
 for n in own:
  if (path/(n+'.lean')).exists():source_pool.setdefault(n,(path/(n+'.lean'),path/(n+'.olean'),key))
source_pool.setdefault('HullCheckMeters',(H/'HullCheckMeters.lean',FC/'HullCheckMeters.olean','classifier_checker_reuse'))
# Every differing duplicate object is checked against the already sealed bridge
# records; source identity remains mandatory, including all fee imports.
licensed={e['module']:e for e in ms['completed_ordinary_integration']['version_compatibility']['evidence']}
def add(n):
 if n in entries or n.split('.')[0] in {'Init','Std','Lean'}:return
 assert n in source_pool,('UNLICENSED_MODULE',n)
 p,o,pkg=source_pool[n];assert p.exists() and o.exists(),(n,p,o)
 loaded=next((x/(n+'.olean') for x in paths if (x/(n+'.olean')).exists()),None);assert loaded is not None,n
 assert sha(loaded)==sha(o),('LOADED_OBJECT_DIFFERENCE',n,loaded,o)
 entries[n]=dict(package=pkg,source=str(p.relative_to(R)),source_sha256=sha(p),olean=str(o.relative_to(R)),olean_sha256=sha(o),loaded_olean=str(loaded.relative_to(R)),loaded_sha256=sha(loaded))
 for k in re.findall(r'^import ([A-Za-z0-9_.\x27]+)\s*$',p.read_text(),re.M):add(k)
 for alt in [F,L,H]:
  ap=alt/(n+'.lean');ao=alt/(n+'.olean')
  if ap.exists() and ao.exists() and ap!=p:
   assert sha(ap)==sha(p),('DUPLICATE_SOURCE_DIFFERENCE',n,ap,p)
   if sha(ao)!=sha(loaded):
    c=licensed[n];assert {sha(loaded),sha(ao)}=={c['chosen_olean_sha256'],c['alternative_olean_sha256']},('UNLICENSED_BRIDGE',n,ao)
    assert sha(R/c['record'])==c['record_sha256']
    if c['metadata_bridge']:
     a=c['metadata_bridge'];assert sha(R/a['chosen'])==a['chosen_sha256'] and sha(R/a['alternative'])==a['alternative_sha256'] and a['chosen_sha256']==a['alternative_sha256']
    bridges.append(dict(module=n,loaded=str(loaded.relative_to(R)),alternative=str(ao.relative_to(R)),license=c))
for n in ['Rule5QueryDomains','ClassifierFeeBinding','ClassifierFeePolynomial','LiteralInterface','Hard2RouteSource']:add(n)
assert shutil.disk_usage(D).free>=3*1024**3
(D/'DEPENDENCIES-v1.json').write_text(json.dumps(dict(status='PASS_PINNED_CLOSURE',modules=len(entries),entries=entries,import_paths=[str(x.relative_to(R)) for x in paths],logical_object_bytes=sum((R/e['loaded_olean']).stat().st_size for e in entries.values())),indent=2)+'\n')
(D/'DEPENDENCY-COMPATIBILITY-v1.json').write_text(json.dumps(dict(status='PASS_PINNED_NEW_FEE_AND_ROUTE_CLOSURE',previous=dict(path=str((P/'DEPENDENCY-COMPATIBILITY-v1.json').relative_to(R)),sha256=sha(P/'DEPENDENCY-COMPATIBILITY-v1.json')),bridges=bridges),indent=2)+'\n')
s=(P/'pilot.py').read_text().replace('algorithm-universal233-rule5-execution-20261016T100131Z-pilot-','algorithm-universal233-rule5-closed-20261016T105342Z-pilot-');(D/'pilot.py').write_text(s)
print('PASS_PINNED_CLOSURE',len(entries),'BRIDGES',len(bridges))
