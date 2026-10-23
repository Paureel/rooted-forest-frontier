#!/usr/bin/env python3
"""Problem-specific exact replay/audit extension of the frozen Rule5 harness.
Reuses its producer template and source/AX parser design; same lineage.
No index toolkit instrument covers Lean source-object audit. No dependency rebuild.
"""
from pathlib import Path
import datetime,gzip,hashlib,io,json,os,re,shutil,signal,subprocess,threading,time
D=Path(__file__).resolve().parent;R=D.parents[5];old=D/'build';new=D/'build';POOL=R/'research/rmaf/algorithm/universal233/ordinary_dispatch/rule5_selected_local_work_20261016T090023Z/imports';Q=R/'results/algorithm-universal233-rule5-selected-20261016T090023Z-freeze-20261016T092100151815Z'
T=R/'research/rmaf/monitoring/rule5-next-20261016T100131Z/RULE5-EXECUTION-TARGET-v1.json'
TEMPLATE=R/'results/algorithm-universal233-rule5-local-work-replay-20261015T213618556319Z/OBProducer0.lean'
ALLOW={'Classical.choice','Quot.sound','propext'};FLOOR=3*1024**3;RAW=64*1024**2;TOTAL=128*1024**2

def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def pin(p,h):
 if sha(p)!=h:raise ValueError('SOURCE_OLEAN_PIN_MISMATCH|'+str(p))
pin(T,'d1ed931067c76e99935e907171514588ec444d36ec569336740f3c9cd1efc1e3');target=json.loads(T.read_text())
for e in target['allowed_packages'].values():pin(R/e['manifest'],e['sha256'])
preservation=[]
for package,e in target['allowed_packages'].items():
 m=json.loads((R/e['manifest']).read_text())
 for item in m.get('immutable_files',[]):
  path=R/item['path'];pin(path,item['sha256']);st=path.stat()
  preservation.append(dict(package=package,path=item['path'],sha256=item['sha256'],mode=st.st_mode,inode=st.st_ino))
(D/'PRESERVATION-v1.json').write_text(json.dumps(preservation,indent=2)+'\n')
assert shutil.disk_usage(D).free>=FLOOR
O=R/'results'/('algorithm-universal233-rule5-execution-20261016T100131Z-freeze-'+datetime.datetime.now(datetime.timezone.utc).strftime('%Y%m%dT%H%M%S%fZ'));O.mkdir();(D/'LAST-FREEZE.txt').write_text(str(O)+'\n')
rec=dict(status='RUNNING_AUTHOR_REPLAY',scope='Actual common and paid execution source spines; all five runSelected arms and strict dispatch; closed general agreement K. Classifier primitives and distinct LiteralProps fee remain explicit; full native forest work is the completed implemented counter. No native or full2.33 acceptance',main='OPEN',whole_rule5_local='SOURCE_COMPOSITION_WITH_DISTINCT_PRIMITIVE_DOMAINS_AND_IMPLEMENTED_FOREST_DEBIT',independent_acceptance=False,native_semantics=False,runs=[],controls={},producer_audits=[],body_qualification='All non-theorem and opaque bodies retained; only theorem proof text omitted, with actual proof references and AX closures traversed',limits=dict(seconds=30,lean_mib=3072,raw_output_bytes=RAW,logical_directory_bytes=TOTAL,free_disk_bytes=FLOOR),template=dict(path=str(TEMPLATE.relative_to(R)),sha256=sha(TEMPLATE)))
def save():(O/'certificate.json').write_text(json.dumps(rec,indent=2)+'\n')
def limits():
 free=shutil.disk_usage(O).free;used=sum(p.stat().st_size for p in O.iterdir() if p.is_file())
 assert free>=FLOOR,('DISK_FLOOR',free)
 assert used<=TOTAL,('LOGICAL_DIRECTORY_CAP',used)
 rec['resources']=dict(free_bytes=free,logical_bytes=used)
def run(n,build=False,want=0):
 limits();start=time.monotonic();reason=[];count=0
 cmd=[str(R/'bootloops-lean'),'-M3072']+(['-o',str(O/(n+'.olean'))] if build else [])+[str(O/(n+'.lean'))]
 proc=subprocess.Popen(cmd,cwd=O,env=dict(os.environ,LEAN_PATH=os.pathsep.join(map(str,[O]+PATHS))),stdout=subprocess.PIPE,stderr=subprocess.STDOUT,start_new_session=True);stop=threading.Event()
 def kill(why):
  reason.append(why)
  try:os.killpg(proc.pid,signal.SIGTERM)
  except ProcessLookupError:pass
 def watch():
  while not stop.wait(.1):
   if time.monotonic()-start>30:kill('TIMEOUT_30S');return
   if shutil.disk_usage(O).free<FLOOR:kill('LIVE_DISK_FLOOR');return
 watcher=threading.Thread(target=watch,daemon=True);watcher.start()
 try:
  with gzip.open(O/(n+'.log.gz'),'wb') as z:
   while True:
    b=proc.stdout.readline(16*1024**2+1)
    if not b:break
    count+=len(b);z.write(b)
    if len(b)>16*1024**2 or count>RAW:kill('OUTPUT_CAP');break
  code=proc.wait(timeout=5)
 finally:stop.set();watcher.join()
 rec['runs'].append(dict(module=n,exit=code,wanted=want,seconds=time.monotonic()-start,raw_bytes=count,stop=reason));save()
 assert not reason,(n,reason)
 assert code==want,(n,code,want)
 return O/(n+'.log.gz')
def audit_source(mods):
 s=TEMPLATE.read_text();assert s.startswith('import ClosedPayload\n');s=s.replace('import ClosedPayload\n',''.join('import '+n+'\n' for n in mods),1)
 needle='let expected : List Name := [`ClosedPayload]';assert needle in s
 return s.replace(needle,'let expected : List Name := ['+', '.join('`'+n for n in mods)+']',1)
def parse(lines,mods,allowed):
 rows=[];summ=[];seen=set();paths={}
 for line in lines:
  line=line.rstrip('\r\n')
  if line.startswith('SUMMARY|'):
   _,m,n=line.split('|');summ.append((m,int(n)))
  elif line.startswith('PATH|'):
   _,m,p=line.split('|',2);paths[m]=p
  elif line.startswith('PRODUCERJSON|'):
   x=json.loads(line.split('|',1)[1]);key=(x['producer'],x['index']);assert key not in seen,'DUPLICATE_ROW';seen.add(key)
   assert x['resolved_origin']!='UNATTRIBUTED';assert x['kind']!='axiom' or x['name'] in ALLOW,'CUSTOM_AXIOM'
   assert set(x['axiom_references'])<=ALLOW,'DEPENDENCY_AXIOM'
   assert x['theorem_body_text_omitted']==(x['kind']=='theorem'),'BODY_SCOPE'
   if x['kind']=='opaque':assert x['body'] is not None,'OPAQUE_BODY_OMITTED'
   rows.append({k:x[k] for k in ['producer','index','name','resolved_origin','kind','references','axiom_references']}|dict(type_sha256=hashlib.sha256(x['type'].encode()).hexdigest(),body_sha256=None if x['body'] is None else hashlib.sha256(x['body'].encode()).hexdigest()))
 assert len(summ)==len(mods) and {m for m,n in summ}==set(mods),'MISSING_OR_DUPLICATE_SUMMARY'
 assert seen=={(m,i) for m,n in summ for i in range(n)},'MISSING_ROW'
 assert set(mods)<=set(paths),'MISSING_PATH'
 for m,p in paths.items():
  p=Path(p).resolve()
  if m in deps:assert p==(R/deps[m]['loaded_olean']).resolve(),'FOREIGN_DEPENDENCY_PATH'
  else:assert p==(O/(m+'.olean')).resolve() if m in allowed else p.is_relative_to(R/'.runtime/elan/toolchains'),'FOREIGN_PATH'
 return rows,summ,paths
def audit(n,mods,allowed,want=0):
 (O/(n+'.lean')).write_text(audit_source(mods));log=run(n,want=want)
 if want:return log
 with gzip.open(log,'rt') as f:return parse(f,mods,allowed)
# Pin every frozen source/object and each exact loaded object. Imports were
# source-compared before composition; this is not an unchecked path union.
deprec=json.loads((D/'DEPENDENCIES-v1.json').read_text());deps=deprec['entries'];PATHS=[R/p for p in deprec['import_paths']]
for n,e in deps.items():
 for k in ['source','olean']:pin(R/e[k],e[k+'_sha256'])
 pin(R/e['loaded_olean'],e['loaded_sha256'])
own=['CommonOutsideSource', 'CommonPaidSource', 'CommonPaidBounds', 'CommonGuardedSource', 'CommonExecutionBinding', 'CommonCallBinding', 'CommonSourceDebit', 'PaidForestCandidates', 'PaidForestPretest', 'PaidForestCandidateWork', 'PaidForestPretestWork', 'PaidCurrentSource', 'PaidArcPartition', 'PaidArcWork', 'PaidGuardSource', 'PaidGuardWork', 'PaidPlanSource', 'PaidRequestsSource', 'PaidPlanWork', 'PaidAnswerLedger', 'PaidPlanPolynomial', 'PaidRequestWork', 'PaidBestSource', 'PaidExecutionBounds', 'PaidSelectedExecution', 'Rule5SelectedSource', 'Rule5SourceBounds', 'ExecutionControls']
identities=[]
for n in own:
 p=D/(n+'.lean');ob=old/(n+'.olean');assert p.exists() and ob.exists()
 identities.append(dict(path=str(p.relative_to(R)),sha256=sha(p),mode=p.stat().st_mode,inode=p.stat().st_ino))
 for q in [p,ob]:
  dest=O/q.name;shutil.copy2(q,dest);dest.chmod(0o444)
(O/'lean-toolchain').write_bytes((old/'lean-toolchain').read_bytes())
visited=set(deps)|set(own)
rec['dependencies']=deps;rec['source_identity']=identities;rec['own_modules']=own;rec['dependency_pool']=dict(paths=deprec['import_paths'],logical_bytes=deprec['logical_object_bytes']);save()
fixtures={
 'R5CleanA':'import Std\ntheorem R5Shared : True := True.intro\n',
 'R5CleanB':'import Std\ntheorem R5Shared : True := True.intro\ntheorem R5Own : (2:Nat)+3=5 := by decide\n',
 'R5Hostile':'import Std\naxiom R5Shared : True\ntheorem R5CleanOwn : True := True.intro\n',
 'R5Private':'import Std\nprivate axiom hidden : False\n',
 'R5Unused':'import Std\naxiom unused : True\ntheorem ownClean : True := True.intro\n',
 'R5Opaque':'import Std\nopaque R5Number : Nat := 7\nopaque R5Proof : True := True.intro\n',
 'R5Foreign':'import Std\naxiom R5ForeignAx : Nat\n',
 'R5OpaqueBad':'import R5Foreign\nnoncomputable opaque R5Bad : Nat := R5ForeignAx\n'}
allowed=set(visited)|set(fixtures)
try:
 for n,s in fixtures.items():(O/(n+'.lean')).write_text(s);run(n,True)
 for i,mods in enumerate([['R5CleanA','R5CleanB'],['R5CleanB','R5CleanA']]):
  rows,_,_=audit('R5CleanAudit'+str(i),mods,allowed);assert len([r for r in rows if r['name']=='R5Shared'])==2
  rec['controls']['clean_order'+str(i)]='PASS_TWO_STORED_PRODUCERS'
 for i,mods in enumerate([['R5CleanA','R5Hostile'],['R5Hostile','R5CleanA'],['R5Private'],['R5Unused']]):
  log=audit('R5HostileAudit'+str(i),mods,allowed,1)
  with gzip.open(log,'rt') as f:assert 'REJECT_DIRECT_CUSTOM_AXIOM|' in f.read()
  rec['controls']['hostile'+str(i)]='CAUGHT'
 rows,_,_=audit('R5OpaqueAudit',['R5Opaque'],allowed);assert len([r for r in rows if r['kind']=='opaque' and r['body_sha256']])==2
 rec['controls']['opaque_body_retention']='TWO_RETAINED'
 log=audit('R5OpaqueBadAudit',['R5OpaqueBad'],allowed,1)
 with gzip.open(log,'rt') as f:assert 'REJECT_DEPENDENCY_CUSTOM_AXIOM|' in f.read()
 rec['controls']['opaque_dependency_axiom']='CAUGHT'
 with gzip.open(O/'R5CleanAudit0.log.gz','rt') as f:clean=f.read()
 first=re.search(r'^PRODUCERJSON\|.*$',clean,re.M).group()
 for tag,bad in [('missing_row',clean.replace(first+'\n','',1)),('duplicate_row',clean+first+'\n'),('foreign_path',clean.replace('PATH|R5CleanA|'+str(O/'R5CleanA.olean'),'PATH|R5CleanA|/tmp/foreign/R5CleanA.olean',1))]:
  try:parse(io.StringIO(bad),['R5CleanA','R5CleanB'],allowed)
  except AssertionError:rec['controls'][tag]='CAUGHT'
  else:raise AssertionError('CORRUPTION_SURVIVED|'+tag)
 firstdep=next(iter(deps.values()))
 for tag,p in [('dependency_source',R/firstdep['source']),('dependency_olean',R/firstdep['olean'])]:
  try:pin(p,'0'*64)
  except ValueError:rec['controls'][tag]='CAUGHT'
  else:raise AssertionError('CORRUPTION_SURVIVED|'+tag)
 try:
  assert hashlib.sha256((audit_source(['R5CleanA'])+' ').encode()).hexdigest()==hashlib.sha256(audit_source(['R5CleanA']).encode()).hexdigest(),'ADAPTED_BYTE_MISMATCH'
 except AssertionError:rec['controls']['adapted_bytes']='CAUGHT'
 else:raise AssertionError('ADAPTED_CORRUPTION_SURVIVED')
 (O/'R5True.lean').write_text('import Std\nexample : (2:Nat)+3=5 := by decide\n');run('R5True')
 (O/'R5False.lean').write_text('import Std\nexample : (2:Nat)+3=6 := by decide\n');log=run('R5False',want=1)
 with gzip.open(log,'rt') as f:assert f.read().count('is false')==1
 rec['controls']['true_false']='PASS_REJECT';save();print('PASS_FRESH_AUDIT_CONTROLS',flush=True)
 # Fresh source compilation of own modules only; dependency objects stay fixed.
 for n in own:
  (O/(n+'.olean')).chmod(0o644)
  log=run(n,True);print('REPLAYED_OWN',n,flush=True)
  if n=='ExecutionControls':
   with gzip.open(log,'rt') as f:out=f.read()
   marker='("PASS_EXECUTION_SOURCE_CONTROLS", 35, true)'
   assert marker in out and ', false)' not in out,'RUNTIME_CONTROL_FAILED'
   rec['controls'][n]='RUNTIME_TRUE_CHECKED'
 (O/'ExecutionFalse.lean').write_bytes((D/'ExecutionFalse.lean').read_bytes());log=run('ExecutionFalse',want=1)
 with gzip.open(log,'rt') as f:assert f.read().count('is false')==8
 rec['controls']['eight_false_execution_claims']='EIGHT_REJECTED'
 allrows=[]
 for i,n in enumerate(own):
  rows,summary,paths=audit('R5Producer'+str(i),[n],allowed);allrows+=rows;rec['producer_audits'].append(dict(module=n,occurrences=len(rows)));save();print('AUDITED_OWN',n,len(rows),flush=True)
 for key in ['outside_reply_value', 'outside_reply_work', 'run_paid_value', 'run_paid_local', 'guarded_value', 'guarded_local', 'common_value', 'common_local_on_jobs', 'common_source_split', 'current_query_value', 'current_answer_split', 'current_prefix_work', 'forest_pretest_value', 'forest_pretest_work', 'best_additional_value', 'arc_from_work', 'arc_partition_payload', 'current_guard_value', 'current_guard_work', 'raw_plan_value', 'raw_plan_work', 'request_for_value', 'requests_work', 'answers_value', 'answers_calls_native', 'request_state_caps', 'best_for_value', 'best_for_prefix_work', 'solve_selected_value', 'solve_selected_prefix_work', 'paid_selected_source_split', 'run_selected_source_value', 'run_selected_source_split', 'run_selected_local_bound', 'dispatch_source_value', 'dispatch_source_split']:
  assert any(r['name']=='Universal233.Rule5ExecutionSource.'+key for r in allrows),key
 with gzip.open(O/'producer-occurrences.json.gz','wt') as f:json.dump(allrows,f,separators=(',',':'))
 rec['axiom_union']=sorted({a for row in allrows for a in row['axiom_references']});rec['stored_producer_occurrences']=len(allrows)
 for e in identities:
  p=R/e['path'];assert sha(p)==e['sha256'] and p.stat().st_ino==e['inode'] and p.stat().st_mode==e['mode'],'ORIGINAL_SOURCE_CHANGED'
 for e in preservation:
  path=R/e['path'];pin(path,e['sha256']);st=path.stat()
  assert st.st_ino==e['inode'] and st.st_mode==e['mode'],'PRIOR_MODE_INODE_CHANGED'
 rec['prior_immutable_occurrences_matched']=len(preservation)
 rec['status']='PASS_AUTHOR_COMMON_PAID_EXECUTION_AND_SELECTED_SOURCE_STAGE';limits();save()
 (D/'LATEST-REPLAY-v1.json').write_text(json.dumps(dict(receipt=str(O.relative_to(R)),certificate_sha256=sha(O/'certificate.json')),indent=2)+'\n')
 for p in O.iterdir():
  if p.is_file():p.chmod(0o444)
 print('PASS_AUTHOR_COMMON_PAID_EXECUTION_AND_SELECTED_SOURCE_STAGE',len(own),len(allrows),O,flush=True)
except Exception as e:
 rec['status']='FAIL_RETAINED';rec['failure']=repr(e);save();print('FAIL_RETAINED',repr(e),O,flush=True);raise
