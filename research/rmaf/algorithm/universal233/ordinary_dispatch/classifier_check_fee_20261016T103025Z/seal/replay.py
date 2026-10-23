#!/usr/bin/env python3
"""One-problem extension of frozen capped Rule5 replay and OBProducer0 auditor.
Same lineage, not independent. No general toolkit instrument covers this source
interface; upstream auditor bytes and all dependency objects remain unchanged.
"""
from pathlib import Path
import datetime,gzip,hashlib,json,os,shutil,signal,subprocess,threading,time
D=Path(__file__).resolve().parent;R=D.parents[5]
PRE=R/'results/algorithm-universal233-rule5-remaining-20261016T092622Z-freeze-20261016T095618897390Z'
Q=R/'results/algorithm-universal233-rule5-selected-20261016T090023Z-freeze-20261016T092100151815Z'
P=R/'research/rmaf/algorithm/universal233/ordinary_dispatch/rule5_selected_local_work_20261016T090023Z/imports'
T=R/'research/rmaf/monitoring/next-20261016T103025Z/CLASSIFIER-CHECK-FEE-TARGET-v1.json'
TEMPLATE=R/'results/algorithm-universal233-rule5-local-work-replay-20261015T213618556319Z/OBProducer0.lean'
LIT=R/'results/algorithm-universal233-paid-literal-20261016T100131Z-freeze-20261016T101642140379Z';H=D/'checker-imports'
FLOOR=3*1024**3;RAW=64*1024**2;LINE=16*1024**2;COMPRESSED=16*1024**2;TOTAL=128*1024**2
ALLOW={'Classical.choice','propext','Quot.sound'}
own=['ClassifierRequestMeter','ClassifierFeePolynomial','ClassifierFeeBinding','ClassifierFeeControls']
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def pin(p,h):
 if sha(p)!=h:raise ValueError('PIN_MISMATCH|'+str(p))
pin(T,'5c53b262c2a938e3f0d1037a4a8cc7f4a3787fa1735be65f67155d48d3997d8c')
target=json.loads(T.read_text())
for e in target['allowed_packages'].values():pin(R/e['manifest'],e['sha256'])
before=json.loads((D/'PRESERVATION-BEFORE-v1.json').read_text())
for e in before:
 p=R/e['path'];pin(p,e['sha256']);s=p.stat();assert (s.st_mode,s.st_ino)==(e['mode'],e['inode'])
deprec=json.loads((D/'DEPENDENCIES-v1.json').read_text());deps=deprec['entries']
for e in deps.values():
 for kind in ['source','olean']:pin(R/e[kind],e[kind+'_sha256'])
 pin(R/e['loaded_olean'],e['loaded_sha256'])
rem=json.loads((R/target['allowed_packages']['common_setup_paid_outer']['manifest']).read_text())
for n in rem['own_modules']:
 src=PRE/(n+'.lean');obj=PRE/(n+'.olean')
 deps[n]=dict(source=str(src.relative_to(R)),source_sha256=sha(src),olean=str(obj.relative_to(R)),olean_sha256=sha(obj),loaded_olean=str(obj.relative_to(R)),loaded_sha256=sha(obj))
O=R/'results'/('algorithm-universal233-classifier-fee-20261016T103025Z-freeze-'+datetime.datetime.now(datetime.timezone.utc).strftime('%Y%m%dT%H%M%S%fZ'));O.mkdir();(D/'LAST-FREEZE.txt').write_text(str(O)+'\n')
rec=dict(version=1,status='RUNNING_AUTHOR_REPLAY',independent=False,native=False,whole_rule5=False,full233=False,runs=[],controls={},own_modules=own,source_identity=[],dependencies=deps,template=dict(path=str(TEMPLATE.relative_to(R)),sha256=sha(TEMPLATE)),limits=dict(seconds=30,lean_mib=3072,raw_bytes=RAW,line_bytes=LINE,compressed_bytes=COMPRESSED,logical_bytes=TOTAL,disk_floor_bytes=FLOOR))
def save():(O/'certificate.json').write_text(json.dumps(rec,indent=2)+'\n')
def resources():
 free=shutil.disk_usage(O).free;used=sum(x.stat().st_size for x in O.iterdir() if x.is_file())
 assert free>=FLOOR,('DISK_FLOOR',free)
 assert used<=TOTAL,('DIRECTORY_CAP',used)
 rec['resources']=dict(free_bytes=free,logical_bytes=used)
def run(n,build=False,want=0):
 resources();start=time.monotonic();reason=[];count=0;out=[]
 cmd=[str(R/'bootloops-lean'),'-M3072']+(['-o',str(O/(n+'.olean'))] if build else [])+[str(O/(n+'.lean'))]
 p=subprocess.Popen(cmd,cwd=O,env=dict(os.environ,LEAN_PATH=os.pathsep.join(map(str,[O,LIT,PRE,Q,P,H]))),stdout=subprocess.PIPE,stderr=subprocess.STDOUT,start_new_session=True);stop=threading.Event()
 def kill(why):
  if not reason:reason.append(why)
  try:os.killpg(p.pid,signal.SIGTERM)
  except ProcessLookupError:pass
 def watch():
  while not stop.wait(.1):
   if time.monotonic()-start>30:kill('TIMEOUT_30S');return
   if shutil.disk_usage(O).free<FLOOR:kill('LIVE_DISK_FLOOR');return
   if sum(x.stat().st_size for x in O.iterdir() if x.is_file())>TOTAL:kill('DIRECTORY_CAP');return
   if (O/(n+'.log.gz')).exists() and (O/(n+'.log.gz')).stat().st_size>COMPRESSED:kill('COMPRESSED_CAP');return
 w=threading.Thread(target=watch,daemon=True);w.start()
 try:
  with gzip.open(O/(n+'.log.gz'),'wb') as z:
   while True:
    b=p.stdout.readline(LINE+1)
    if not b:break
    count+=len(b);z.write(b);out.append(b)
    if len(b)>LINE:kill('LINE_CAP');break
    if count>RAW:kill('RAW_CAP');break
  code=p.wait(timeout=5)
 finally:stop.set();w.join()
 rec['runs'].append(dict(module=n,exit=code,wanted=want,seconds=time.monotonic()-start,raw_bytes=count,stop=reason));save()
 assert not reason,(n,reason)
 assert code==want,(n,code,want)
 return b''.join(out).decode(errors='replace')
def audit_source(mods):
 s=TEMPLATE.read_text();assert s.startswith('import ClosedPayload\n');s=s.replace('import ClosedPayload\n',''.join('import '+n+'\n' for n in mods),1)
 needle='let expected : List Name := [`ClosedPayload]';assert needle in s
 return s.replace(needle,'let expected : List Name := ['+', '.join('`'+n for n in mods)+']',1)
def parse(text,mods,allowed):
 rows=[];summ=[];seen=set();paths={}
 for line in text.splitlines():
  if line.startswith('SUMMARY|'):
   _,m,n=line.split('|');summ.append((m,int(n)))
  elif line.startswith('PATH|'):
   _,m,p=line.split('|',2);paths[m]=p
  elif line.startswith('PRODUCERJSON|'):
   x=json.loads(line.split('|',1)[1]);key=(x['producer'],x['index']);assert key not in seen,'DUPLICATE_ROW';seen.add(key)
   assert x['resolved_origin']!='UNATTRIBUTED','UNATTRIBUTED'
   assert x['kind']!='axiom' or x['name'] in ALLOW,'CUSTOM_AXIOM'
   assert set(x['axiom_references'])<=ALLOW,'DEPENDENCY_AXIOM'
   assert x['theorem_body_text_omitted']==(x['kind']=='theorem'),'BODY_SCOPE'
   if x['kind']=='opaque':assert x['body'] is not None,'OPAQUE_BODY_OMITTED'
   rows.append(x)
 assert len(summ)==len(mods) and {m for m,n in summ}==set(mods),'SUMMARY'
 assert seen=={(m,i) for m,n in summ for i in range(n)},'MISSING_ROW'
 assert set(mods)<=set(paths),'MISSING_PATH'
 for m,p in paths.items():
  p=Path(p).resolve()
  if m in deps:assert p==(R/deps[m]['loaded_olean']).resolve(),'FOREIGN_DEPENDENCY_PATH'
  elif m in allowed:assert p==(O/(m+'.olean')).resolve(),'FOREIGN_PATH'
  else:assert p.is_relative_to(R/'.runtime/elan/toolchains'),'FOREIGN_PATH'
 return rows,paths
fixtures={
 'LDCleanA':'import Std\ntheorem LDShared : True := True.intro\n',
 'LDCleanB':'import Std\ntheorem LDShared : True := True.intro\ntheorem LDOwn : (2:Nat)+3=5 := by decide\n',
 'LDHostile':'import Std\naxiom LDShared : True\n',
 'LDPrivate':'import Std\nprivate axiom hidden : False\n',
 'LDUnused':'import Std\naxiom unused : True\ntheorem cleanOwn : True := True.intro\n',
 'LDOpaque':'import Std\nopaque LDNumber : Nat := 7\nopaque LDProof : True := True.intro\n',
 'LDForeign':'import Std\naxiom LDForeignAx : Nat\n',
 'LDOpaqueBad':'import LDForeign\nnoncomputable opaque LDBad : Nat := LDForeignAx\n'}
allowed=set(own)|set(fixtures)
def audit(n,mods,want=0):
 (O/(n+'.lean')).write_text(audit_source(mods));s=run(n,want=want)
 return (s,None) if want else (s,parse(s,mods,allowed))
try:
 (O/'lean-toolchain').write_bytes((P/'lean-toolchain').read_bytes())
 # Test the unchanged producer instrument first, on preregistered controls.
 for n,s in fixtures.items():(O/(n+'.lean')).write_text(s);run(n,True)
 for i,mods in enumerate([['LDCleanA','LDCleanB'],['LDCleanB','LDCleanA']]):
  _,(rows,_)=audit('LDCleanAudit'+str(i),mods);assert sum(x['name']=='LDShared' for x in rows)==2
  rec['controls']['producer_clean_order'+str(i)]='TWO_STORED_PRODUCERS'
 for i,n in enumerate(['LDHostile','LDPrivate','LDUnused','LDOpaqueBad']):audit('LDHostileAudit'+str(i),[n],1);rec['controls'][n]='REJECTED'
 _,(op,_)=audit('LDOpaqueAudit',['LDOpaque']);assert len([x for x in op if x['kind']=='opaque' and x['body'] is not None])==2;rec['controls']['opaque']='TWO_BODIES_RETAINED'
 # Compile only new own sources; never rebuild a dependency.
 for n in own:
  src=D/(n+'.lean');assert n not in deps
  st=src.stat();rec['source_identity'].append(dict(path=str(src.relative_to(R)),sha256=sha(src),mode=st.st_mode,inode=st.st_ino))
  shutil.copy2(src,O/src.name);run(n,True)
  (O/src.name).chmod(0o444)
 # Clean arithmetic twin plus deliberately impossible claims.
 for n in ['ClassifierFalseArithmetic','ClassifierFalseEmbedding']:
  shutil.copy2(D/(n+'.lean'),O/(n+'.lean'));s=run(n,want=1);assert 'error' in s;rec['controls'][n]='REJECTED_FRESH_SOURCE'
 text,(rows,paths)=audit('ClassifierProducerAudit',own)
 # Reached frozen source instance and exact fee consumers, without dependency census.
 frozen=['AdmittedCheckCalls','TreeCheckMeters','HullCheckMeters','FinalClassifierWork']
 _,(frows,fpaths)=audit('FrozenCheckAudit',frozen)
 rec['stored_own_occurrences']=len(rows);rec['stored_frozen_occurrences']=len(frows)
 rec['axiom_union']=sorted(set(a for x in rows+frows for a in x['axiom_references']))
 assert not any('sorryAx' in x['references'] for x in rows+frows)
 # Parser corruption controls use the complete successful output, on copies.
 def must_reject(label,s):
  try:parse(s,own,allowed)
  except (AssertionError,ValueError,KeyError):rec['controls'][label]='CAUGHT'
  else:raise AssertionError('UNCATCHED_'+label)
 lines=text.splitlines();ix=next(i for i,x in enumerate(lines) if x.startswith('PRODUCERJSON|'))
 must_reject('missing_row','\n'.join(lines[:ix]+lines[ix+1:]))
 must_reject('duplicate_row',text+'\n'+lines[ix])
 forged=lines.copy();row=json.loads(forged[ix].split('|',1)[1]);row['kind']='axiom';row['name']='customFalse';forged[ix]='PRODUCERJSON|'+json.dumps(row);must_reject('custom_axiom','\n'.join(forged))
 forged=lines.copy();row=json.loads(forged[ix].split('|',1)[1]);row['axiom_references']=['customFalse'];forged[ix]='PRODUCERJSON|'+json.dumps(row);must_reject('dependency_axiom','\n'.join(forged))
 foreign=lines.copy();pi=next(i for i,x in enumerate(foreign) if x.startswith('PATH|ClassifierRequestMeter|'));foreign[pi]='PATH|ClassifierRequestMeter|/private/tmp/foreign.olean';must_reject('foreign_path','\n'.join(foreign))
 runtime=gzip.open(O/'ClassifierFeeControls.log.gz','rt').read();assert '("CLASSIFIER_FEE_CONTROLS", 18, true)' in runtime;assert '("REQUEST_BILLS", 156, 182, 74, 42, "CAP_N2", 64540034)' in runtime
 rec['controls']['runtime']='18_OF_18';rec['request_bills']=[156,182,74,42];rec['cap_N2']=64540034
 # Store declaration summaries while preserving the full actual bodies in gzip.
 def summary(x):return {k:x[k] for k in ['producer','index','name','resolved_origin','kind','references','axiom_references']}|dict(type_sha256=hashlib.sha256(x['type'].encode()).hexdigest(),body_sha256=None if x['body'] is None else hashlib.sha256(x['body'].encode()).hexdigest())
 (O/'stored-declarations.json').write_text(json.dumps([summary(x) for x in rows+frows],indent=2)+'\n')
 for e in before:
  p=R/e['path'];pin(p,e['sha256']);st=p.stat();assert (st.st_mode,st.st_ino)==(e['mode'],e['inode'])
 for e in rec['source_identity']:
  p=R/e['path'];pin(p,e['sha256']);st=p.stat();assert (st.st_mode,st.st_ino)==(e['mode'],e['inode'])
 rec['preserved_immutable_occurrences']=len(before);rec['status']='PASS_AUTHOR_SOURCE_PRIMITIVE_MODEL';resources();save()
except BaseException as e:
 rec['status']='FAIL_RETAINED';rec['error']=repr(e);save();raise
print(json.dumps({k:rec[k] for k in ['status','stored_own_occurrences','stored_frozen_occurrences','axiom_union','controls','resources']},indent=2));print(O)
