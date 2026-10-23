from pathlib import Path
import datetime,hashlib,json,os,re,shutil,subprocess,time
D=Path(__file__).resolve().parent;R=D.parents[5]
P=R/'results/algorithm-universal233-ordinary-source-pool-20261015T144445575127Z';C=R/'results/algorithm-universal233-state-cherry-20261015T101755Z'
B=R/'results'/('algorithm-universal233-ordinary-common-reduction-'+datetime.datetime.now(datetime.timezone.utc).strftime('%Y%m%dT%H%M%S%fZ'));B.mkdir()
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
rec=dict(status='AUTHOR_COMMON_REDUCTION_STAGING',all_main_milestones='OPEN',independent_acceptance=False,controls={},sources=[],mapping=[],runs=[],input_pins={})
def save():(B/'certificate.json').write_text(json.dumps(rec,indent=2)+'\n')
# The same exact adapted-byte equality rule as the completed resolver.
known={hashlib.sha256(b'import A\nvalue\n').hexdigest():'A'}
assert known.get(hashlib.sha256(b'import A\nvalue\n').hexdigest())=='A'
assert known.get(hashlib.sha256(b'import A\ncorrupted\n').hexdigest()) is None
rec['controls']['adapted_exact_twin']='DEDUPLICATED';rec['controls']['corrupted_adapted_bytes']='NOT_DEDUPLICATED'
for p in [Path(__file__),D/'TARGET-v1.md',P/'construction.json',R/'research/rmaf/algorithm/universal233/state_cherry_completion/CHERRY-MANIFEST-v1.json']:rec['input_pins'][str(p.relative_to(R))]=sha(p)
# Validate every selected input member that is actually consumed below.
manifest=json.loads((R/'research/rmaf/algorithm/universal233/state_cherry_completion/CHERRY-MANIFEST-v1.json').read_text());mp={e['path']:e['sha256'] for e in manifest['immutable_files']}
base=json.loads((P/'construction.json').read_text())['source_modules'];chosen={};bybytes={};source={};resolved={};active=set()
for e in base:
 p=P/(e['module']+'.lean');assert sha(p)==e['sha256'];chosen[e['module']]=dict(module=e['module'],path=str(p.relative_to(R)),sha256=e['sha256'],origins=e['origins']);bybytes[e['sha256']]=e['module'];source[('pool',e['module'])]=p
for p in C.glob('*.lean'):source[('cherry',p.stem)]=p
source[('own','CommonDispatch')]=D/'CommonDispatch.lean'
def resolve(key):
 if key in resolved:return resolved[key]
 assert key not in active;active.add(key);p=source[key]
 if key[0]=='cherry':assert mp.get(str(p.relative_to(R)))==sha(p),('CHERRY_PIN',str(p))
 changes={};lines=[]
 for line in p.read_text().splitlines(keepends=True):
  if line.startswith('import '):
   m=re.fullmatch(r'import ([A-Za-z0-9_\'.]+)\s*',line);assert m;dep=m[1]
   if dep.split('.')[0] not in {'Std','Lean','Init'}:
    depkey=(key[0],dep)
    if depkey not in source:
     depkey=('cherry',dep) if ('cherry',dep) in source and key[0]=='own' else ('pool',dep)
    assert depkey in source,('MISSING_SOURCE',key,dep)
    new=resolve(depkey)
    if new!=dep:line='import '+new+'\n';changes[dep]=new
  lines.append(line)
 data=''.join(lines).encode();h=hashlib.sha256(data).hexdigest()
 if h in bybytes:n=bybytes[h]
 else:
  n=key[1]
  if n in chosen:n='CommonCherry'+n
  assert n not in chosen;bybytes[h]=n
  chosen[n]=dict(module=n,path=str(p.relative_to(R)),sha256=h,original_sha256=sha(p),import_adaptations=changes,origins=[dict(package=key[0],module=key[1])]);(B/(n+'.lean')).write_bytes(data)
 resolved[key]=n;active.remove(key);rec['mapping'].append(dict(package=key[0],original_module=key[1],selected_module=n));return n
try:
 # Own module uses selected old modules except its StateExpand import.
 root=resolve(('own','CommonDispatch'));order=[];seen=set()
 def visit(n):
  if n in seen:return
  q=B/(n+'.lean')
  if not q.exists():q.write_bytes((R/chosen[n]['path']).read_bytes())
  assert sha(q)==chosen[n]['sha256']
  for dep in re.findall(r'^import ([A-Za-z0-9_\'.]+)\s*$',q.read_text(),re.M):
   if dep.split('.')[0] not in {'Std','Lean','Init'}:visit(dep)
  seen.add(n);order.append(n)
 visit(root);rec['sources']=[chosen[n] for n in order];save();(B/'lean-toolchain').write_bytes((P/'lean-toolchain').read_bytes())
 for n in order:
  assert shutil.disk_usage(R).free>=3*(1<<30),'FREE_SPACE_MARGIN_STOP'
  if n in {e['module'] for e in base}:
   p=P/(n+'.olean');shutil.copyfile(p,B/p.name);rec['runs'].append(dict(module=n,mode='PINNED_COMPLETED_BINARY_COPY',source_sha256=sha(P/(n+'.lean')),olean_sha256=sha(p)));save()
  else:
   start=time.monotonic();z=subprocess.run([str(R/'bootloops-lean'),'-o',str(B/(n+'.olean')),str(B/(n+'.lean'))],cwd=B,env=dict(os.environ,LEAN_PATH=str(B)),capture_output=True,text=True,timeout=30)
   log=B/(n+'.log');log.write_text(z.stdout+z.stderr);rec['runs'].append(dict(module=n,mode='FRESH_SOURCE_BUILD',exit=z.returncode,seconds=time.monotonic()-start,log_sha256=sha(log)));save();print('BUILD',n,z.returncode,flush=True);assert z.returncode==0,(n,z.stdout+z.stderr)
 rec['status']='PASS_AUTHOR_COMMON_SOURCE_CLOSURE';save()
except BaseException as e:rec.update(status='FAILED_NOT_ACCEPTED',error=repr(e));save();raise
finally:(D/'LATEST-BUILD-v1.json').write_text(json.dumps(dict(directory=str(B.relative_to(R)),certificate_sha256=sha(B/'certificate.json')),indent=2)+'\n')
