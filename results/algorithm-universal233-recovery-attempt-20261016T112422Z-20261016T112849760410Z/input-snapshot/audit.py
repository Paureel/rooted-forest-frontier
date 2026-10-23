"""Owned source/stored DAG/axiom audit; prior extractor remains unchanged."""
from pathlib import Path
import gzip,json,shutil,sys,time
sys.dont_write_bytecode=True
import run,dag_instrument as ins
D=run.D;R=run.R;O=run.O;sha=run.sha;B='OrdinaryDispatch.RecoveryAttemptBits.'
mods=['RAReceipt','RAState','RAAttempt','RAInterface','RAControls']
C=O/'AUDIT-CERTIFICATE-v3.json';F=O/'producer-records-v1'
rec={'status':'RUNNING_AUTHOR','independent_credit':0,'instrument':{'path':str((D/'dag_instrument.py').relative_to(R)),'sha256':sha(D/'dag_instrument.py'),'owned_adaptation':True,'prior_extractor_modified':False},'controls':{},'modules':[]}
def save():C.write_text(json.dumps(rec,indent=2)+'\n')
def deps():
 for e in json.loads((D/'DEPENDENCIES-BEFORE-v1.json').read_text())['members']:
  p=R/e['path'];s=p.stat();assert sha(p)==e['sha256'] and oct(s.st_mode&0o777)==e['mode'] and s.st_ino==e['inode'] and s.st_dev==e['device'],str(p)
def current(n,want=0):
 p=D/(n+'.lean');assert sha(O/p.name)==sha(p),'SOURCE_PIN_MISMATCH'
 qs=[]
 for q in O.glob(n+'-*.run.json'):
  r=json.loads(q.read_text())
  if r.get('exit')==want and not r.get('stop_reasons') and r.get('source_sha256')==sha(p):qs.append(q)
 assert qs,n
 q=max(qs,key=lambda p:p.stat().st_mtime_ns);return q,json.loads(q.read_text())
def closure(graph,start):
 seen=set();stack=[start]
 while stack:
  n=stack.pop()
  if n in seen:continue
  seen.add(n);row=graph.get(n)
  if row and row['kind']!='theorem':stack+=row['references']
 return seen
def witness(graph,start,goal):
 stack=[(start,[])];seen=set()
 while stack:
  n,p=stack.pop()
  if n==goal:return p+[n]
  if n in seen:continue
  seen.add(n);row=graph.get(n)
  if row and row['kind']!='theorem':stack += [(x,p+[n]) for x in row['references']]
 return None
save()
try:
 deps()
 for n in mods:
  q,r=current(n);rec['modules'].append({'module':n,'source':str((D/(n+'.lean')).relative_to(R)),'source_sha256':sha(D/(n+'.lean')),'olean':str((O/(n+'.olean')).relative_to(R)),'olean_sha256':sha(O/(n+'.olean')),'receipt':str(q.relative_to(R)),'receipt_sha256':sha(q),'peak_rss_bytes':r['peak_rss_bytes']})
 q,r=current('RAControls');s=gzip.decompress((R/r['log']).read_bytes()).decode();positives=['rootFirst','rootPaid','duplicate','entire','successful','prunedKept','attemptCount','noVisit','noOutput','addressStructural','finiteRefusal','overflowWitness','copiesIdentity','closesPaid','continuationState','refusalCounterOne']
 for n in positives:assert B+'Controls.'+n+' :' in s,n
 rec['controls']['positive']={'count':len(positives),'names':positives,'receipt':str(q.relative_to(R))}
 # All deliberately false source claims must receive a false diagnosis.
 out=run.run('RAFalseControls',1);assert out.count('is false')==8,out
 rec['controls']['false_claims']=8
 # Bounded exporter pilot before full audit; stored full expression DAGs only.
 P=O/'producer-pilot-v1';P.mkdir();(O/'RAPilotAudit.lean').write_text(ins.source(['RAReceipt'],['RAReceipt'],P));run.run('RAPilotAudit');pilot=ins.parse(P,['RAReceipt'],O)
 rec['pilot_occurrences']=len(pilot);save()
 F.mkdir();(O/'RABoundedAudit.lean').write_text(ins.source(['RAControls'],mods,F));run.run('RABoundedAudit',audit=True);rows=ins.parse(F,mods,O);names={x['name']:x for x in rows}
 required=['refusalReceipt_value','refusalReceipt_words','bumpAttempt_value','bumpAttempt_work','bumpAttempt_words','bumpAttempt_lifetime','copyGroups_value','copyGroups_work','callOwned_value','callOwned_lifetime','callOwned_work','attemptBits_value','attemptBits_words','attemptBits_source_work','root_refusal_priority','successful_attempt_lifetime','represented_attempt','actual_zero_fuel_child']
 for n in required:assert names[B+n]['kind']=='theorem',n
 refs={'represented_attempt':['attemptBits_value','attemptBits_source_work','attemptBits_words'],'attemptBits_value':['callOwned_value'],'attemptBits_source_work':['callOwned_work'],'callOwned_work':['copyGroups_work','bumpAttempt_work'],'actual_zero_fuel_child':['attemptBits_value']}
 for n,rs in refs.items():
  for x in rs:assert B+x in names[B+n]['references'],(n,x)
 prior=[];prior_records=[]
 for stem,sub in [('recovery_scalar_lift_20261016T095748Z','producer-records-v2'),('recovery_represented_initial_20261016T103025Z','producer-records-v2'),('recovery_represented_control_20261016T105553Z','producer-records-v1')]:
  pm=R/'research/rmaf/algorithm/universal233/ordinary_dispatch'/stem/'FINAL-MANIFEST-v1.json';m=json.loads(pm.read_text());po=R/m['canonical_receipt'];found=[]
  for mod in m['source_modules']:
   n=mod['module'];data=json.loads(gzip.decompress((po/sub/(n+'.json.gz')).read_bytes()));assert [(x['producer'],x['index']) for x in data]==[(n,j) for j in range(len(data))];found+=data
  prior+=found;prior_records.append({'manifest':str(pm.relative_to(R)),'sha256':sha(pm),'occurrences':len(found)})
 graph={x['name']:x for x in prior+rows}
 runtime=['refusalReceipt','prunedReceipt','bumpAttempt','copyGroups','callOwned','rootAddress','attemptBits','prunedAttempt']
 forbidden=['OrdinaryDispatch.RecoveryBits.'+x for x in ['encode','decode','viewGroup','viewTree','viewOutput']]+[B+x for x in ['viewRefusal','viewReceipt','ReceiptWords']]+['OrdinaryDispatch.RecoveryControlBits.'+x for x in ['rawGroups','rawMixed','groupFee','groupsCells','choiceCells','viewChoice']]+['Classical.choose']
 for n in runtime:
  assert names[B+n]['kind']=='definition' and names[B+n]['body_dag'] is not None
  assert not set(forbidden)&closure(graph,B+n),(n,set(forbidden)&closure(graph,B+n))
 calls={'bumpAttempt':['OrdinaryDispatch.RecoveryInitialBits.stepLength','OrdinaryDispatch.RecoveryInitialBits.closeBits'],'copyGroups':['OrdinaryDispatch.RecoveryBits.copyGroup'],'callOwned':[B+'copyGroups',B+'bumpAttempt','OrdinaryDispatch.RecoveryBits.copyGroup','OrdinaryDispatch.RecoveryBits.copyBits','OrdinaryDispatch.RecoveryBits.copyArrays','OrdinaryDispatch.RecoveryInitialBits.closeTree','OrdinaryDispatch.RecoveryControlBits.closeGroups','OrdinaryDispatch.RecoveryInitialBits.closeArrays'],'attemptBits':[B+'rootAddress',B+'refusalReceipt','OrdinaryDispatch.RecoveryControlBits.addressContains','OrdinaryDispatch.RecoveryControlBits.eraseBits',B+'callOwned']}
 paths={}
 for n,rs in calls.items():
  paths[n]={}
  for x in rs:
   p=witness(graph,B+n,x);assert p,(n,x);paths[n][x]=p
 # Planted corruptions preserve each rejected input in its own directory.
 for flavor in ['missing','duplicate','changed_hash']:
  X=O/('producer-'+flavor+'-control-v1');shutil.copytree(F,X)
  first=next(X.glob('RAReceipt-*.json.gz'))
  if flavor=='missing':first.unlink()
  elif flavor=='duplicate':shutil.copyfile(first,X/'extra.json.gz')
  else:
   raw=json.loads(gzip.decompress(first.read_bytes()));raw['index']=-1;first.write_bytes(gzip.compress(json.dumps(raw).encode()))
  try:ins.parse(X,mods,O)
  except (AssertionError,FileNotFoundError):rec['controls'][flavor+'_producer']='CAUGHT'
  else:raise AssertionError(flavor+'_CONTROL_FAILED')
 try:assert sha(D/'RAReceipt.lean')=='0'*64,'SOURCE_PIN_MISMATCH'
 except AssertionError:rec['controls']['source_hash_comparator']='CAUGHT'
 (O/'RAHostile.lean').write_text('import RAInterface\naxiom hostile : False\ntheorem hostileUse : False := hostile\n');run.run('RAHostile')
 H=O/'producer-hostile-v1';H.mkdir();(O/'RAHostileAudit.lean').write_text(ins.source(['RAHostile'],['RAHostile'],H));out=run.run('RAHostileAudit',1,audit=True);assert 'REJECT_PRODUCER_OCCURRENCE' in out;ins.parse(H,['RAHostile'],O,hostile=True);rec['controls']['custom_axiom']='CAUGHT'
 for n in ['Work','RCStorage','RILifetime','RSBinaryCompare']:
  try:run.run(n)
  except AssertionError as e:assert 'REFUSE_DEPENDENCY_REBUILD' in str(e)
  else:raise AssertionError('NO_REBUILD_GUARD_FAILED')
 rec['controls']['no_rebuild']=4
 deps()
 for e in rec['modules']:assert sha(R/e['source'])==e['source_sha256'] and sha(R/e['olean'])==e['olean_sha256']
 runs=[json.loads(p.read_text()) for p in O.glob('*.run.json')];accepted=[x for x in runs if x.get('module') in mods and x['exit']==0 and not x['stop_reasons']]
 rec.update(status='PASS_AUTHOR_PERSISTENT_ATTEMPT_STEP_RUN_OPEN',stored_occurrences=len(rows),axiom_union=sorted({a for x in rows for a in x['axiom_references']}),interfaces=required,source_body_call_paths=paths,runtime_projection_and_desired_fee_closure_absent=True,prior_own_closure=prior_records,bounded_export={'chunk_bytes_cap':4194304,'maximum_chunk_bytes':max(len(gzip.decompress(p.read_bytes())) for p in F.glob('*.gz')),'maximum_expression_nodes':max(len(d['nodes']) for row in rows for d in [row['type_dag'],row['body_dag']] if d),'full_nonproof_DAG':True,'theorem_proof_text_omitted_actual_full_proof_AX_walk':True},resource_failures_preserved=[str(p.relative_to(R)) for p in O.glob('RESOURCE*')]+[str(p.relative_to(R)) for p in O.glob('*.run.json') if json.loads(p.read_text()).get('stop_reasons')],maximum_measured_rss_bytes=max(x['peak_rss_bytes'] for x in runs),maximum_measured_seconds=max(x['seconds'] for x in runs),compressed_bytes=sum(p.stat().st_size for p in O.rglob('*.gz')),dependency_rebuilds=0,first_gap='Actual persistent step finish-output construction, copied choice close, combine/prefixRoot and receipt append; then finite represented run fuel, full-prefix counter fits/caps and whole recovery lifetime',skipped=['actual represented step/run/fuel/receipt combine and whole recovery bit coefficient','native compiler/IR/allocator/metadata arithmetic correspondence','independent acceptance','global ordinary/forest/Rule4/Rule5 campaigns','full2.33/base/novelty acceptance'])
 assert set(rec['axiom_union'])<=ins.ALLOW;save();print(rec['status'],len(rows),rec['axiom_union'])
except BaseException as e:rec.update(status='FAIL_RETAINED',error=repr(e));save();raise
