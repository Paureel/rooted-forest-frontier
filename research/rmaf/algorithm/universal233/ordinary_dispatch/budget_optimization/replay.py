#!/usr/bin/env python3
"""One-shot source-bound author replay. New modules only; no dependency rebuilds."""
from pathlib import Path
import datetime,gzip,hashlib,io,json,os,re,shutil,signal,subprocess,threading,time
D=Path(__file__).resolve().parent;R=D.parents[5]
MAN=R/'research/rmaf/algorithm/universal233/ordinary_dispatch/fast_ordinary_recursion/FINAL-MANIFEST-v1.json'
MSHA='0f806c00eacdc8d3d12ffb9c38406edd0363eb6b5a235897506880fe05efcb8c'
C=R/'results/algorithm-universal233-fast-ordinary-recursion-replay-20261015T205325296780Z'
TEMPLATE=C/'OBProducer0.lean';ALLOW={'Classical.choice','Quot.sound','propext'}
OWN=['BOForest','BOScan','BOOptimize','BOCost','BOConditional','BOControls'];FLOOR=3*1024**3;TOTAL=128*1024**2
O=R/'results'/('algorithm-universal233-budget-optimization-replay-'+datetime.datetime.now(datetime.timezone.utc).strftime('%Y%m%dT%H%M%S%fZ'));O.mkdir()
rec={'status':'RUNNING_AUTHOR','independent_acceptance':False,'global_233_runtime':'OPEN','novelty':False,'dependency_rebuilds':0,'runs':[],'controls':{},'audits':[],'resource_policy':{'timeout_seconds':60,'disk_floor_bytes':FLOOR,'directory_cap_bytes':TOTAL},'same_lineage_reuse':True}
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def save():(O/'certificate.json').write_text(json.dumps(rec,indent=2)+'\n')
def pin(p,h):
 if sha(p)!=h:raise ValueError('SOURCE_PIN_MISMATCH|'+str(p))
def limits():
 free=shutil.disk_usage(O).free;used=sum(p.stat().st_size for p in O.iterdir() if p.is_file())
 if free<FLOOR or used>TOTAL:raise RuntimeError('RESOURCE_FLOOR_OR_CAP')
 rec['resources']={'free_bytes':free,'directory_bytes':used}
def run(n,build=False,want=0):
 limits();assert not (C/(n+'.lean')).exists(),'REFUSE_DEPENDENCY_REBUILD'
 started=time.monotonic();p=subprocess.Popen([str(R/'bootloops-lean')]+(['-o',str(O/(n+'.olean'))] if build else [])+[str(O/(n+'.lean'))],cwd=O,env=dict(os.environ,LEAN_PATH=str(O)+':'+str(C)),stdout=subprocess.PIPE,stderr=subprocess.STDOUT,start_new_session=True)
 stop=threading.Event();reason=[]
 def kill(why):
  reason.append(why)
  try:os.killpg(p.pid,signal.SIGTERM)
  except ProcessLookupError:pass
 def watch():
  while not stop.wait(.1):
   if time.monotonic()-started>60:kill('TIMEOUT_60S');return
   if shutil.disk_usage(O).free<FLOOR:kill('DISK_FLOOR_3GIB');return
 th=threading.Thread(target=watch,daemon=True);th.start();count=0
 try:
  with gzip.open(O/(n+'.log.gz'),'wb') as z:
   while True:
    b=p.stdout.readline(16*1024**2+1)
    if not b:break
    z.write(b);count+=len(b)
    if len(b)>16*1024**2 or count>64*1024**2:kill('OUTPUT_CAP');break
  code=p.wait(timeout=5)
 finally:stop.set();th.join()
 rec['runs'].append({'module':n,'build':build,'exit':code,'expected':want,'seconds':time.monotonic()-started,'raw_bytes':count,'stop_reasons':reason});save()
 assert code==want and not reason,(n,code,reason)
 return gzip.open(O/(n+'.log.gz'),'rt').read()
def audit_source(mod):
 s=TEMPLATE.read_text();s=s.replace('import EarlySelector\n','import '+mod+'\n',1)
 s=s.replace('let expected : List Name := [`EarlySelector]','let expected : List Name := [`'+mod+']',1)
 assert 'ci.getUsedConstantsAsSet' in s and 'allowOpaque := true' in s
 return s
def parse(s,mod):
 rows=[];summ=[];paths={};seen=set()
 for line in s.splitlines():
  if line.startswith('SUMMARY|'):
   _,m,n=line.split('|');summ.append((m,int(n)))
  elif line.startswith('PATH|'):
   _,m,p=line.split('|',2);paths[m]=str(Path(p).resolve())
  elif line.startswith('PRODUCERJSON|'):
   row=json.loads(line.split('|',1)[1]);key=(row['producer'],row['index'])
   assert key not in seen,'DUPLICATE_ROW';seen.add(key)
   assert row['resolved_origin']!='UNATTRIBUTED','UNATTRIBUTED'
   assert row['kind']!='axiom' or row['name'] in ALLOW,'CUSTOM_AXIOM'
   assert set(row['axiom_references'])<=ALLOW,'DEPENDENCY_AXIOM'
   assert row['theorem_body_text_omitted']==(row['kind']=='theorem'),'BODY_SCOPE'
   if row['kind']=='opaque':assert row['body'] is not None,'OPAQUE_BODY_OMITTED'
   rows.append(row)
 assert len(summ)==1 and summ[0][0]==mod,'MISSING_SUMMARY'
 assert seen=={(mod,i) for i in range(summ[0][1])},'MISSING_ROW'
 assert paths.get(mod)==str((O/(mod+'.olean')).resolve()),'FOREIGN_PRODUCER_PATH'
 for name,path in paths.items():
  p=Path(path)
  if p.parent==O:assert p.name in {n+'.olean' for n in OWN+['BOAuditTrue','BOAuditHostile']},'FOREIGN_LOCAL_MODULE'
  elif p.is_relative_to(C):assert path in licensed,'UNLICENSED_DEPENDENCY';pin(p,licensed[path])
  else:assert p.is_relative_to(R/'.runtime/elan/toolchains'),'FOREIGN_IMPORT'
 return rows,paths
try:
 limits();pin(MAN,MSHA);mf=json.loads(MAN.read_text());licensed={str((R/f['path']).resolve()):f['sha256'] for f in mf['immutable_files']}
 def allpins():
  for f in mf['immutable_files']:pin(R/f['path'],f['sha256'])
 allpins();rec['dependency_manifest']={'path':str(MAN.relative_to(R)),'sha256':MSHA,'immutable_members_verified':len(mf['immutable_files'])}
 assert str(TEMPLATE.resolve()) in licensed
 rec['audit_template']={'path':str(TEMPLATE.relative_to(R)),'sha256':sha(TEMPLATE)}
 rec['source_entries']=[]
 for n in OWN+['BOFalse']:
  s=(D/(n+'.lean')).read_bytes();assert not re.search(rb'\b(sorry|admit|native_decide)\b',s),'FORBIDDEN_PROOF_TOKEN'
  (O/(n+'.lean')).write_bytes(s);rec['source_entries'].append({'module':n,'source':str((D/(n+'.lean')).relative_to(R)),'source_sha256':sha(D/(n+'.lean'))})
 (O/'lean-toolchain').write_bytes((C/'lean-toolchain').read_bytes());save()
 for n in OWN:
  out=run(n,True);rec['source_entries'][OWN.index(n)]['olean_sha256']=sha(O/(n+'.olean'))
  if n=='BOControls':
   assert '("PASS_WRAPPER_CONTROLS", true)' in out and '("CAUGHT_WRAPPER_CORRUPTIONS", true)' in out
   assert out.count('("corrupted_actual_singleton_conversion", false)')==1
   assert out.count('("dropped_failed_trial", false)')==1
   rec['controls']['actual_clean_and_corruption']='8_CLEAN_2_CORRUPTIONS_CAUGHT'
  print('BUILT_NEW_ONLY',n,flush=True)
 false=run('BOFalse',want=1);assert false.count('is false')==4;rec['controls']['false_propositions']='4_REJECTED_AS_FALSE'
 (O/'BOAuditTrue.lean').write_text('import Std\ntheorem BOTrue : (2:Nat)+3=5 := by decide\n')
 (O/'BOAuditHostile.lean').write_text('import Std\naxiom BOUntrusted : True\n')
 run('BOAuditTrue',True);run('BOAuditHostile',True)
 allrows=[];clean=None
 for n in OWN+['BOAuditTrue']:
  an='BOProducer'+n;(O/(an+'.lean')).write_text(audit_source(n));out=run(an)
  rows,paths=parse(out,n);allrows+=rows;rec['audits'].append({'module':n,'stored_producers':len(rows),'olean_path':paths[n]});save()
  if n=='BOAuditTrue':clean=out
  print('AUDITED_NEW_ONLY',n,len(rows),flush=True)
 (O/'BOProducerHostile.lean').write_text(audit_source('BOAuditHostile'));hostile=run('BOProducerHostile',want=1)
 assert 'REJECT_DIRECT_CUSTOM_AXIOM|' in hostile;rec['controls']['custom_axiom']='CAUGHT'
 first=re.search(r'^PRODUCERJSON\|.*$',clean,re.M).group(0)
 for tag,bad in [('missing_row',clean.replace(first+'\n','',1)),('duplicate_row',clean+first+'\n'),('foreign_path',clean.replace('PATH|BOAuditTrue|'+str(O/'BOAuditTrue.olean'),'PATH|BOAuditTrue|/tmp/foreign/BOAuditTrue.olean',1))]:
  try:parse(bad,'BOAuditTrue')
  except AssertionError:rec['controls'][tag]='CAUGHT'
  else:raise AssertionError('CORRUPTION_SURVIVED|'+tag)
 try:pin(D/'BOOptimize.lean','0'*64)
 except ValueError:rec['controls']['source_hash']='CAUGHT'
 else:raise AssertionError('HASH_CORRUPTION_SURVIVED')
 required=['optimization_exact','actual_query_count','total_charge_exact','conditional_233','conditional_233_polynomial','scan_success','scan_upper_success']
 for n in required:assert any(row['name']=='OrdinaryDispatch.BudgetOptimization.'+n for row in allrows),n
 with gzip.open(O/'producer-occurrences.json.gz','wt') as z:json.dump(allrows,z,separators=(',',':'))
 for e in rec['source_entries']:pin(R/e['source'],e['source_sha256'])
 allpins();limits();rec.update(status='PASS_AUTHOR_NEW_SOURCE_OLEAN_PRODUCER_BOUND',dependency_members_after_verified=len(mf['immutable_files']),axiom_union=sorted({a for row in allrows for a in row['axiom_references']}),interfaces=required,stored_producers=len(allrows),first_missing_consumer='Actual FastOrdinary.solve source/bit work perQuery for every successful and failed budget, with primitive interpretation of queryWork and wrapper charges. Global runtime remains OPEN.')
 save();(O/'VERDICT.txt').write_text('PASS_AUTHOR_NEW_SOURCE_OLEAN_PRODUCER_BOUND\nWrapper functional correctness and conditional cost conversion only. Global 2.33 runtime OPEN; independent acceptance pending.\n')
 (D/'LATEST-REPLAY-v1.json').write_text(json.dumps({'receipt':str(O.relative_to(R)),'certificate_sha256':sha(O/'certificate.json')},indent=2)+'\n')
 print(rec['status'],rec['stored_producers'],rec['axiom_union'],O,flush=True)
except BaseException as exc:
 rec['status']='FAIL_RETAINED';rec['failure']=repr(exc);save();print('FAIL_RETAINED',O,repr(exc),flush=True);raise
