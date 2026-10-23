from pathlib import Path
import datetime,hashlib,json,os,re,resource,selectors,shutil,signal,subprocess,time
D=Path(__file__).resolve().parent;R=D.parents[5];P=R/'results/algorithm-universal233-ordinary-source-pool-20261015T144445575127Z';B=R/'results'/('algorithm-universal233-fast-source-pool-'+datetime.datetime.now(datetime.timezone.utc).strftime('%Y%m%dT%H%M%S%fZ'));B.mkdir()
FLOOR=3*(1<<30)
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
rec=dict(status='FRESH_IMPORT_CONTROLS',all_main_milestones='OPEN',independent_acceptance=False,full_faster_solver=False,inputs={},controls={},runs=[],source_entries=[],mapping=[])
def save():(B/'certificate.json').write_text(json.dumps(rec,indent=2)+'\n')
def cap():resource.setrlimit(resource.RLIMIT_FSIZE,(128*(1<<20),128*(1<<20)))
def run(root,n,want=0):
 assert shutil.disk_usage(R).free>=FLOOR,'FREE_SPACE_MARGIN_STOP';start=time.monotonic();p=subprocess.Popen([str(R/'bootloops-lean'),'-o',str(root/(n+'.olean')),str(root/(n+'.lean'))],cwd=root,env=dict(os.environ,LEAN_PATH=str(root)),stdout=subprocess.PIPE,stderr=subprocess.STDOUT,preexec_fn=cap,start_new_session=True);sel=selectors.DefaultSelector();sel.register(p.stdout,selectors.EVENT_READ);chunks=[];size=0;stop=None
 while sel.get_map():
  if shutil.disk_usage(R).free<FLOOR:stop='FREE_SPACE_MARGIN_STOP'
  elif time.monotonic()-start>60:stop='COMMAND_60S_CAP'
  elif size>8*(1<<20):stop='STDOUT_8MIB_CAP'
  if stop:os.killpg(p.pid,signal.SIGINT);break
  for key,_ in sel.select(.1):
   b=os.read(key.fd,1<<16)
   if b:chunks.append(b);size+=len(b)
   else:sel.unregister(key.fileobj)
 try:tail=p.communicate(timeout=3)[0]
 except subprocess.TimeoutExpired:os.killpg(p.pid,signal.SIGKILL);tail=p.communicate()[0]
 if tail:chunks.append(tail)
 sel.close();out=b''.join(chunks).decode(errors='replace');log=root/(n+'.log');log.write_text(out);rec['runs'].append(dict(module=n,exit=p.returncode,expected_exit=want,seconds=time.monotonic()-start,resource_stop=stop,source_sha256=sha(root/(n+'.lean')),log=str(log.relative_to(R)),log_sha256=sha(log)));save();assert stop is None,stop;assert p.returncode==want,(n,out[-7000:]);return out
configs=[
 ('common_reduction','ordinary_dispatch/common_reduction/release_v1/COMMON-REDUCTION-MANIFEST-v1.json','bd8621aa7e6b014655afb1c59229c7cdd0bfdcf3bbae86cc30339dde43b5feec','results/algorithm-universal233-ordinary-common-reduction-20261015T185752074314Z',['CommonDispatch']),
 ('child_bindings','ordinary_dispatch/resume_20261015T1810Z/child_consumer_release_v1/CHILD-CONSUMER-MANIFEST-v1.json','81385da329940b0c4fc89262cd2d44dbbfe4c7c28af82a94e32495ade298d5ed','results/algorithm-universal233-ordinary-child-binding-20261015T182851721674Z',['CherryDispatch','Rule4Dispatch']),
 ('orientation','rule5_source_orientation_consumer/FINAL-MANIFEST-v1.json','a27469192042dff5e1001961ed64bac312b3c0f527ba02056263bda19a3b5fd8','results/algorithm-universal233-rule5-source-orientation-replay-20261015T182316Z',['RecursiveConsumers']),
 ('common_ordinary','rule5_common_ordinary_binding/FINAL-MANIFEST-v1.json','9abc8927a932b4d77345adb783db42075821a572d74dab929b90c9e5248024b1','results/algorithm-universal233-rule5-common-ordinary-replay-20261015T190416Z',['OrdinaryBinding']),
 ('paid_ordinary','rule5_paid_ordinary_binding/FINAL-MANIFEST-v1.json','721c3519d3f1b5bb18224681121dc6e501933f941fce6b6b9c36cf3d1f049edb','results/algorithm-universal233-rule5-paid-ordinary-replay-20261015T192240128545Z',['SelectedExact']),
 ('priority','ordinary_dispatch/priority_bridge/FINAL-MANIFEST-v1.json','066d48e2937c4f9beb80c7b4a241734d676f8f2405cff56de65a62191667ef8d','results/algorithm-universal233-ordinary-priority-root-20261015T191026Z',['AdmissionBridge']),
 ('pair','pair_assembly/PAIR-ASSEMBLY-MANIFEST-v1.json','67bf3edef33fca98f6a99d4a4f9dd420b2c98268c31742b901a1478f1b246c57','results/algorithm-universal233-pair-assembly-20261015T093218Z',['GoodPair']),
 ('both_bad','both_bad/BOTH-BAD-MANIFEST-v1.json','da001ef62039c916cf6db24f61c994094b5b1750f5be9130ddaf512ae5fbe20d','results/algorithm-universal233-both-bad-20261015T115125Z',['PlanCover','PlanActualMass','ExecutionWork','CallDecrease']),
 ('all_good','all_good_dp/ALL-GOOD-MANIFEST-v1.json','02ad617e00e9b394f25404b4c89fb47fcf3ca92c1323a49f30313ec31f6e70d6','results/algorithm-universal233-all-good-20261015T113011Z',['ExactMinimum'])]
for p in [Path(__file__),D/'TARGET-v1.md',P/'construction.json']:rec['inputs'][str(p.relative_to(R))]=sha(p)
save();(B/'lean-toolchain').write_bytes((P/'lean-toolchain').read_bytes())
try:
 T=B/'controls';T.mkdir();(T/'lean-toolchain').write_bytes((B/'lean-toolchain').read_bytes())
 fixtures={'DefZero':'namespace FastImporterPlant\ndef value : Nat := 0\nend FastImporterPlant\n','DefOne':'namespace FastImporterPlant\ndef value : Nat := 1\nend FastImporterPlant\n','DefTwin':'namespace FastImporterPlant\ndef value : Nat := 0\nend FastImporterPlant\n','ProofA':'theorem FastImporterProof : True := True.intro\n','ProofB':'theorem FastImporterProof : True := True.intro\n'}
 for n,s in fixtures.items():(T/(n+'.lean')).write_text('import Std\n'+s);run(T,n)
 for n,imps,w in [('ProofTwins',['ProofA','ProofB'],0),('BadLR',['DefZero','DefOne'],1),('BadRL',['DefOne','DefZero'],1),('IdenticalNPTwins',['DefZero','DefTwin'],1)]:
  (T/(n+'.lean')).write_text(''.join('import '+i+'\n' for i in imps));out=run(T,n,w)
  if w:assert 'already declared' in out or 'already been declared' in out or "environment already contains 'FastImporterPlant.value'" in out,(n,out)
  rec['controls'][n]=dict(expected_exit=w,diagnostic='THEOREM_IMPORT_PASS' if w==0 else 'NONPROOF_TWIN_REJECTED')
 # Resolver's rule is literal adapted byte equality, never declaration-type equality.
 assert sha(T/'DefZero.lean')==sha(T/'DefTwin.lean') and sha(T/'DefZero.lean')!=sha(T/'DefOne.lean');rec['controls']['exact_adapted_bytes']='PASS'
 try:assert sha(T/'DefZero.lean')=='corrupted'
 except AssertionError:rec['controls']['corrupted_source_pin']='CAUGHT'
 else:raise AssertionError('CORRUPTED_PIN_ACCEPTED')
 source={};chosen={};bybytes={};resolved={};active=set()
 base=json.loads((P/'construction.json').read_text())['source_modules']
 for e in base:
  p=P/(e['module']+'.lean');assert sha(p)==e['sha256'];source[('base',e['module'])]=(p,e['sha256']);chosen[e['module']]=dict(module=e['module'],sha256=e['sha256'],origins=[dict(package='base',source=str(p.relative_to(R)),source_sha256=e['sha256'],import_adaptations={})]);bybytes[e['sha256']]=e['module']
 for pkg,m,h,root,entries in configs:
  p=R/'research/rmaf/algorithm/universal233'/m;assert sha(p)==h;rec['inputs'][str(p.relative_to(R))]=h;manifest=json.loads(p.read_text());pins={e['path']:e['sha256'] for e in manifest['immutable_files']};root=R/root
  for q in root.glob('*.lean'):
   if str(q.relative_to(R)) in pins:source[(pkg,q.stem)]=(q,pins[str(q.relative_to(R))])
  for n in entries:assert (pkg,n) in source,('CONSUMER_SOURCE_ABSENT',pkg,n)
 def resolve(key):
  if key in resolved:return resolved[key]
  assert key not in active,('IMPORT_CYCLE',key);assert key in source,('MISSING_SOURCE',key);active.add(key);p,h=source[key];assert sha(p)==h;changes={};lines=[]
  for line in p.read_text().splitlines(keepends=True):
   if line.startswith('import '):
    m=re.fullmatch(r'import ([A-Za-z0-9_\'.]+)\s*',line);assert m,('IMPORT_SYNTAX',key,line);dep=m[1]
    if dep.split('.')[0] not in {'Std','Lean','Init'}:
     dk=(key[0],dep);assert dk in source,('PACKAGE_SOURCE_CLOSURE',key,dep);new=resolve(dk)
     if new!=dep:line='import '+new+'\n';changes[dep]=new
   lines.append(line)
  data=''.join(lines).encode();ah=hashlib.sha256(data).hexdigest();origin=dict(package=key[0],source=str(p.relative_to(R)),source_sha256=h,import_adaptations=changes)
  if ah in bybytes:n=bybytes[ah];chosen[n]['origins'].append(origin)
  else:
   n=key[1]
   if n in chosen:n='Fast'+''.join(s.title() for s in key[0].split('_'))+n
   assert n not in chosen,('MODULE_ALIAS_COLLISION',key,n);bybytes[ah]=n;chosen[n]=dict(module=n,sha256=ah,origins=[origin]);(B/(n+'.lean')).write_bytes(data)
  resolved[key]=n;active.remove(key);rec['mapping'].append(dict(package=key[0],original_module=key[1],selected_module=n));return n
 roots=[]
 for pkg,m,h,root,entries in configs:
  for n in entries:roots.append(resolve((pkg,n)))
 # Named primitive whole-source covers are part of the same literal base pool.
 for n in ['HardPaid','LocalSelector']:assert ('base',n) in source;roots.append(resolve(('base',n)))
 order=[];seen=set()
 def visit(n):
  if n in seen:return
  p=B/(n+'.lean')
  if not p.exists():p.write_bytes((P/(n+'.lean')).read_bytes())
  assert sha(p)==chosen[n]['sha256']
  for dep in re.findall(r'^import ([A-Za-z0-9_\'.]+)\s*$',p.read_text(),re.M):
   if dep.split('.')[0] not in {'Std','Lean','Init'}:visit(dep)
  seen.add(n);order.append(n)
 for n in roots:visit(n)
 (B/'FastImports.lean').write_text(''.join('import '+n+'\n' for n in dict.fromkeys(roots)))
 rec.update(status='AUTHOR_ACTUAL_CONSUMER_SOURCE_BUILD',source_entries=[chosen[n] for n in order],consumer_modules=list(dict.fromkeys(roots)),imported_modules=len(order),source_pool_runtime_claim=False);save();print('STAGED',len(order),'named consumers',len(set(roots)),flush=True)
 for i,n in enumerate(order):
  run(B,n);print('BUILT',i+1,len(order),n,flush=True)
 run(B,'FastImports');rec['status']='PASS_AUTHOR_FAST_CONSUMER_SOURCES_ONE_ROOT_PENDING_PRODUCER_AUDIT';save();print(rec['status'],len(order),flush=True)
except BaseException as e:rec.update(status='FAILED_NOT_ACCEPTED',error=repr(e));save();raise
finally:(D/'LATEST-BUILD-v1.json').write_text(json.dumps(dict(directory=str(B.relative_to(R)),certificate_sha256=sha(B/'certificate.json')),indent=2)+'\n')
