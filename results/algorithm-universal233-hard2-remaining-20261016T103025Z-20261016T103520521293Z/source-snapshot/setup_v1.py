from pathlib import Path
import datetime,hashlib,json,os,re,shutil
D=Path(__file__).resolve().parent;R=D.parents[5]
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
T=R/'research/rmaf/monitoring/next-20261016T103025Z/MAIN-HARD2-REMAINING-TARGET-v1.json';assert sha(T)=='1d7630704bd30255e2c3b8f09fdac57e1790d43760ae211230d5a4f874866e29';t=json.loads(T.read_text());inputs={};manifests={}
for key in ['hard2_front','actual_recovery_source','optimizer_fees','early','optimizer','checker']:
 e=t['allowed_packages'][key];p=R/e['manifest'];assert sha(p)==e['sha256'];m=json.loads(p.read_text());manifests[key]=m
 for f in m['immutable_files']:assert sha(R/f['path'])==f['sha256'];inputs[f['path']]=f['sha256']
 inputs[e['manifest']]=e['sha256']
old=manifests['hard2_front'];P=R/old['canonical_build']
contexts=[R/manifests['actual_recovery_source']['canonical_receipt'],R/manifests['optimizer_fees']['canonical_receipt'],R/'results/algorithm-universal233-early-resume-20261016T083330Z-20261016T083634190186Z',R/'results/algorithm-universal233-budget-optimization-replay-20261015T213529360638Z',R/'results/algorithm-universal233-forest-check-root-20261015T211023Z']
pinned=inputs.copy()
for m in manifests.values():
 for e in m.get('original_files',[]):
  if isinstance(e,dict):pinned[e['path']]=e['sha256']
resolved={};order=[]
def visit(n):
 if n in resolved:return
 found=[(C/(n+'.lean'),C/(n+'.olean')) for C in contexts if (C/(n+'.lean')).exists() and (C/(n+'.olean')).exists()];assert found,('NO_CONTEXT',n)
 p,o=found[0]
 for f in [p,o]:assert str(f.relative_to(R)) in pinned and sha(f)==pinned[str(f.relative_to(R))],('UNPINNED_CONTEXT',str(f))
 resolved[n]=(p,o)
 for dep in re.findall(r'^import ([A-Za-z0-9_\'.]+)\s*$',p.read_text(),re.M):
  if dep.split('.')[0] not in {'Std','Lean','Init'}:visit(dep)
 order.append(n)
visit('RWInitial')
assert shutil.disk_usage(R).free>=3*(1<<30)
B=R/'results'/('algorithm-universal233-hard2-remaining-20261016T103025Z-'+datetime.datetime.now(datetime.timezone.utc).strftime('%Y%m%dT%H%M%S%fZ'));B.mkdir();sources=[];diffs=[];new=[]
for p in sorted(P.glob('*.lean')):
 o=P/(p.stem+'.olean')
 if not o.exists():continue
 for f in [p,o]:assert not f.stat().st_mode&0o222;os.link(f,B/f.name)
 sources.append(dict(module=p.stem,source=str(p.relative_to(R)),source_sha256=sha(p),olean=str(o.relative_to(R)),olean_sha256=sha(o)))
for n in order:
 p,o=resolved[n];bp=B/p.name;bo=B/o.name
 if bp.exists():
  assert sha(bp)==sha(p),('SOURCE_CONFLICT',n)
  if sha(bo)!=sha(o):diffs.append(dict(module=n,source=str(p.relative_to(R)),source_sha256=sha(p),original_olean=str(o.relative_to(R)),original_olean_sha256=sha(o),chosen_olean_sha256=sha(bo)))
 else:
  for f in [p,o]:
   q=B/f.name
   if f.stat().st_mode&0o222:shutil.copyfile(f,q);q.chmod(0o444)
   else:os.link(f,q)
  new.append(n)
shutil.copyfile(P/'lean-toolchain',B/'lean-toolchain')
s=dict(status='PASS_EXACT_LICENSED_CONSUMER_SEED_COMPATIBILITY_AUDIT_PENDING',target_sha256=sha(T),previous_manifest=t['previous_completed'],sources=sources,new_modules=new,source_conflicts=[],object_identity_differences=diffs,recovery_original_contexts=[str(C.relative_to(R)) for C in contexts],recovery_closure=[dict(module=n,source=str(resolved[n][0].relative_to(R)),source_sha256=sha(resolved[n][0]),olean=str(resolved[n][1].relative_to(R)),olean_sha256=sha(resolved[n][1])) for n in order],inputs=inputs,independent_acceptance=False,all_main_milestones='OPEN')
(B/'SEED.json').write_text(json.dumps(s,indent=2)+'\n');(D/'BUILD-v1.json').write_text(json.dumps(dict(directory=str(B.relative_to(R)),seed_sha256=sha(B/'SEED.json')),indent=2)+'\n');print(B,'old',len(sources),'recoveryclosure',len(order),'new',new,'differences',[e['module'] for e in diffs])
