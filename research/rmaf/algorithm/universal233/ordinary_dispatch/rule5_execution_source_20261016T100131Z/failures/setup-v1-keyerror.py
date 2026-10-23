from pathlib import Path
import json,hashlib,re,shutil
D=Path(__file__).resolve().parent;R=D.parents[5]
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
T=R/'research/rmaf/monitoring/rule5-next-20261016T100131Z/RULE5-EXECUTION-TARGET-v1.json'
assert sha(T)=='d1ed931067c76e99935e907171514588ec444d36ec569336740f3c9cd1efc1e3';t=json.loads(T.read_text());manifests={}
for k,e in t['allowed_packages'].items():
 p=R/e['manifest'];assert sha(p)==e['sha256'];manifests[k]=json.loads(p.read_text())
P=R/'research/rmaf/algorithm/universal233/ordinary_dispatch/rule5_remaining_local_work_20261016T092622Z';O=R/manifests['common_setup_paid_outer']['canonical_build'];M=R/manifests['ordinary_selected_K']['canonical_build'];S=R/manifests['selected_forest_arms']['canonical_build'];POOL=R/manifests['selected_forest_arms']['dependency_pool']
deps=json.loads((P/'DEPENDENCIES-v1.json').read_text())['entries'];own=manifests['common_setup_paid_outer']['own_modules'];compat={e['module']:e for e in manifests['ordinary_selected_K']['version_compatibility']['evidence']}
C=R/manifests['rule5common']['canonical_build']
paths=[O,S,POOL,M,C];entries={};bridges=[]
def add(n):
 if n in entries or n.split('.')[0] in {'Init','Std','Lean'}:return
 if n in own:p=O/(n+'.lean');o=O/(n+'.olean');package='common_setup_paid_outer'
 elif n in deps:p=R/deps[n]['source'];o=R/deps[n]['loaded_olean'];package='prior_exact_closure'
 elif (M/(n+'.lean')).exists():p=M/(n+'.lean');o=M/(n+'.olean');package='ordinary_selected_K'
 else:p=C/(n+'.lean');o=C/(n+'.olean');package='rule5common'
 assert p.exists() and o.exists(),(n,p,o)
 actual=next((q/(n+'.olean') for q in paths if (q/(n+'.olean')).exists()),None);assert actual==o,(n,actual,o)
 entries[n]=dict(package=package,source=str(p.relative_to(R)),source_sha256=sha(p),olean=str(o.relative_to(R)),olean_sha256=sha(o),loaded_olean=str(o.relative_to(R)),loaded_sha256=sha(o))
 for k in re.findall(r'^import ([A-Za-z0-9_.\x27]+)\s*$',p.read_text(),re.M):add(k)
 alt=M/(n+'.olean');sp=M/(n+'.lean')
 if sp.exists() and p!=sp:
  assert sha(p)==sha(sp),('SOURCE_CONFLICT',n)
  if sha(o)!=sha(alt):
   c=compat[n];assert c['source_sha256']==sha(p)
   assert {sha(o),sha(alt)}=={c['chosen_olean_sha256'],c['alternative_olean_sha256']},('UNLICENSED_OBJECT_PAIR',n)
   assert sha(R/c['record'])==c['record_sha256']
   meta=c['metadata_bridge']
   if meta:
    assert sha(R/meta['chosen'])==meta['chosen_sha256'] and sha(R/meta['alternative'])==meta['alternative_sha256'] and meta['chosen_sha256']==meta['alternative_sha256']
   bridges.append(dict(module=n,loaded=str(o.relative_to(R)),alternative=str(alt.relative_to(R)),licensed_compatibility=c))
for n in ['CommonSetupBinding','PaidDomains','CommonAgreementConsumer','SelectedAgreementBinding','CommonPolynomial']:add(n)
assert shutil.disk_usage(D).free>=3*1024**3
(D/'DEPENDENCIES-v1.json').write_text(json.dumps(dict(status='PASS_EXACT_SOURCE_CLOSURE_WITH_LICENSED_OBJECT_BRIDGES',modules=len(entries),entries=entries,import_paths=[str(p.relative_to(R)) for p in paths],logical_object_bytes=sum((R/e['loaded_olean']).stat().st_size for e in entries.values())),indent=2)+'\n')
(D/'DEPENDENCY-COMPATIBILITY-v1.json').write_text(json.dumps(dict(status='PASS_ALL_21_OBJECT_DIFFERENCES_MATCH_COMPLETED_PARENT_CERTIFICATE',manifest=t['allowed_packages']['ordinary_selected_K'],bridges=bridges),indent=2)+'\n')
s=(P/'pilot.py').read_text();a=s.index("P=R/'");b=s.index(';deps=json.loads',a);s=s[:a]+"PATHS=[R/p for p in json.loads((D/'DEPENDENCIES-v1.json').read_text())['import_paths']];P=PATHS[2]"+s[b:];s=s.replace('[B,Q,P]','[B]+PATHS').replace('algorithm-universal233-rule5-remaining-20261016T092622Z-pilot-','algorithm-universal233-rule5-execution-20261016T100131Z-pilot-');(D/'pilot.py').write_text(s)
print('PASS_PINNED_CLOSURE',len(entries),'LICENSED_BRIDGES',len(bridges))
