#!/usr/bin/env python3
"""One-shot author full-source replay and bounded gzip producer audit.
Uses the completed author's Lean source generator; independent review is absent.
"""
from pathlib import Path
import datetime,gzip,hashlib,importlib.util,io,json,os,re,shutil,subprocess,threading,time
D=Path(__file__).resolve().parent;R=D.parents[4]
P=R/'research/rmaf/algorithm/universal233/rule5_case322/audit.py'
sp=importlib.util.spec_from_file_location('completed_pretest_author_detector',P)
A=importlib.util.module_from_spec(sp);sp.loader.exec_module(A)
STAMP=datetime.datetime.now(datetime.timezone.utc).strftime('%Y%m%dT%H%M%S%fZ')
O=R/'results'/('algorithm-universal233-rule5-paid-selector-replay-'+STAMP);O.mkdir()
RAW=64*1024**2;LINE=16*1024**2;TOTAL=256*1024**2;FLOOR=3*1024**3
rec=dict(status='RUNNING_AUTHOR',all_three_main_milestones='OPEN',independent_acceptance=False,
 novelty=False,improved_base=0,q='k-1',implicit_rho=False,runs=[],controls={},producer_audits=[],
 resource_limits=dict(process_seconds=30,raw_bytes_per_module=RAW,line_bytes=LINE,directory_bytes=TOTAL,free_floor_bytes=FLOOR),
 contact='Completed final paid422 and source orientation releases, prior frozen pretest author instrument; DEVELOPMENT only.')
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def save():(O/'certificate.json').write_text(json.dumps(rec,indent=2)+'\n')
def pin(p,h):
 if sha(p)!=h:raise ValueError('SOURCE_PIN_MISMATCH|'+str(p))
def adapted_pin(s,h):
 if hashlib.sha256(s.encode()).hexdigest()!=h:raise ValueError('ADAPTED_BYTE_MISMATCH')
def limits():
 used=sum(p.stat().st_size for p in O.iterdir() if p.is_file())
 if used>TOTAL:raise RuntimeError('DIRECTORY_BYTE_CAP|'+str(used))
 free=shutil.disk_usage(O).free
 if free<FLOOR:raise RuntimeError('FREE_SPACE_FLOOR|'+str(free))
 rec['resource_usage']=dict(directory_bytes=used,free_bytes=free)
def run(n,build=False,want=0):
 limits();start=time.monotonic()
 p=subprocess.run([str(R/'bootloops-lean')]+(['-o',str(O/(n+'.olean'))] if build else [])+[str(O/(n+'.lean'))],
   cwd=O,env=dict(os.environ,LEAN_PATH=str(O)),text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,timeout=30)
 (O/(n+'.log')).write_text(p.stdout)
 rec['runs'].append(dict(module=n,exit=p.returncode,seconds=time.monotonic()-start));save()
 assert p.returncode==want,(n,p.stdout[-6000:]);return p

def parse_lines(lines,mods,localmods):
 summaries=[];rows=[];paths={};seen=set()
 for line in lines:
  line=line.rstrip('\r\n')
  if line.startswith('SUMMARY|'):
   _,m,n=line.split('|');summaries.append((m,int(n)))
  elif line.startswith('PATH|'):
   _,m,p=line.split('|',2);paths[m]=p
  elif line.startswith('PRODUCERJSON|'):
   r=json.loads(line.split('|',1)[1]);key=(r['producer'],r['index'])
   assert key not in seen,'DUPLICATE_PRODUCER_OCCURRENCE';seen.add(key)
   assert r['resolved_origin']!='UNATTRIBUTED'
   assert r['kind']!='axiom' or r['name'] in A.ALLOW,'DIRECT_CUSTOM_AXIOM'
   assert set(r['axiom_references'])<=A.ALLOW,'DEPENDENCY_CUSTOM_AXIOM'
   assert r.get('theorem_body_text_omitted')==(r['kind']=='theorem'),'BODY_OMISSION_SCOPE'
   if r['kind']=='opaque':assert r['body'] is not None,'OPAQUE_BODY_OMITTED'
   # Full type/body remain in gzip. The compact occurrence file binds each.
   rows.append({k:r[k] for k in ['producer','index','name','resolved_origin','kind','axiom_references']}|
     dict(type_sha256=hashlib.sha256(r['type'].encode()).hexdigest(),
       body_sha256=None if r['body'] is None else hashlib.sha256(r['body'].encode()).hexdigest(),
       references=r['references']))
 assert len(summaries)==len(mods) and {m for m,n in summaries}==set(mods),'MISSING_OR_DUPLICATE_PRODUCER_SUMMARY'
 assert seen=={(m,i) for m,n in summaries for i in range(n)},'MISSING_PRODUCER_OCCURRENCE'
 assert set(mods)<=set(paths),'MISSING_MODULE_PATH'
 for m,p in paths.items():
  p=Path(p).resolve()
  assert p==(O/(m+'.olean')).resolve() if m in localmods else p.is_relative_to(R/'.runtime/elan/toolchains'),'FOREIGN_MODULE_PATH'
 return rows,summaries,paths

def audit_run(name,mods,localmods,want=0):
 limits();(O/(name+'.lean')).write_text(audit_source(mods));start=time.monotonic();raw=0;timed=[False]
 p=subprocess.Popen([str(R/'bootloops-lean'),str(O/(name+'.lean'))],cwd=O,
   env=dict(os.environ,LEAN_PATH=str(O)),stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
 def stop():timed[0]=True;p.kill()
 timer=threading.Timer(30,stop);timer.start()
 try:
  with gzip.open(O/(name+'.log.gz'),'wb',compresslevel=6) as z:
   while True:
    b=p.stdout.readline(LINE+1)
    if not b:break
    raw+=len(b);z.write(b)
    if shutil.disk_usage(O).free<FLOOR:p.kill();raise RuntimeError('STREAM_FREE_SPACE_FLOOR')
    if len(b)>LINE or raw>RAW:p.kill();raise RuntimeError('AUDIT_OUTPUT_CAP|'+name)
  code=p.wait()
 finally:timer.cancel()
 assert not timed[0],('PILOT_TIMEOUT_30S',name)
 rec['runs'].append(dict(module=name,exit=code,seconds=time.monotonic()-start,raw_bytes=raw,
   gzip_bytes=(O/(name+'.log.gz')).stat().st_size));save()
 assert code==want,(name,code)
 if code:return None
 with gzip.open(O/(name+'.log.gz'),'rt') as f:rows,summaries,paths=parse_lines(f,mods,localmods)
 return rows,summaries,paths

def audit_source(mods):
 s=A.audit_source(mods)
 old='("body",toJson (ci.value?.map reprStr))'
 new='("body",toJson (if kind == "theorem" then (none : Option String) else (ci.value? (allowOpaque := true)).map reprStr)), ("theorem_body_text_omitted",toJson (kind == "theorem"))'
 assert old in s
 return s.replace(old,new)

try:
 manifests=[('research/rmaf/algorithm/universal233/rule5_case322_paid_guard/RULE5-CASE322-PAID-GUARD-MANIFEST-v1.json','a1c3805010404da55836b2762b732c48c96132b4038edd074ac3da384a4bc0c1'),('research/rmaf/algorithm/universal233/rule5_source_orientation_consumer/FINAL-MANIFEST-v1.json','a27469192042dff5e1001961ed64bac312b3c0f527ba02056263bda19a3b5fd8'),('research/rmaf/algorithm/universal233/ordinary_dispatch/forest_pretest01/FOREST-PRETEST01-MANIFEST-v1.json','6e79a07b451188ea43a8f380074bff22ee72cc5678ab861d7fdba065e7135602')]
 frozen=[];rec['dependency_manifests']=[]
 for path,h in manifests:
  M=R/path;pin(M,h);rows=json.loads(M.read_text())['immutable_files'];frozen+=rows
  for e in rows:pin(R/e['path'],e['sha256'])
  rec['dependency_manifests'].append(dict(path=path,sha256=h,immutable_files_verified=len(rows)))
 own=['SelectorGeometry','SelectorBuilder','SelectorConsumer','SelectorControls','PaidRequests','SelectorWork','RequestControls']
 entries=json.loads((D/'STACK-PINS.json').read_text())
 for n in own:
  p=D/(n+'.lean');entries.append(dict(module=n,path=str(p.relative_to(R)),sha256=sha(p),adapted_sha256=sha(p),adaptations={}))
 mods=[e['module'] for e in entries];assert len(mods)==len(set(mods))
 for e in entries:
  p=R/e['path'];pin(p,e['sha256']);s=p.read_text();adapted_pin(s,e['adapted_sha256'])
  stripped=re.sub(r'--[^\n]*','',re.sub(r'/\-.*?\-/','',s,flags=re.S))
  assert not re.search(r'\b(sorry|admit|axiom|native_decide)\b',stripped),p
  (O/(e['module']+'.lean')).write_text(s)
 rec['source_entries']=entries;rec['own_modules']=own
 (O/'STACK-PINS.json').write_text(json.dumps(entries,indent=2)+'\n')
 for n in ['TARGET-v1.md','CONTROLS-PIN-v1.md','CONTACT-LEDGER-v1.md','WORKFILE.md']:(O/n).write_bytes((D/n).read_bytes())
 (O/'lean-toolchain').write_bytes((D/'build/lean-toolchain').read_bytes())
 (O/'SelectorFalse.lean').write_bytes((D/'SelectorFalse.lean').read_bytes())
 rec['input_hashes']={str(p.relative_to(R)):sha(p) for p in D.iterdir() if p.is_file() and p.suffix in ['.lean','.py','.md']}
 rec['instrument_hashes']={str(P.relative_to(R)):sha(P),str((P.parent.parent/'rule5_local/audit.py').relative_to(R)):sha(P.parent.parent/'rule5_local/audit.py')}
 rec['body_qualification']='Every non-theorem body, including all opaque bodies, retained in gzip; theorem proof text omitted only, full theorem body references/AX closures retained via ConstantInfo.getUsedConstantsAsSet (allowOpaque true).'
 save()
 for n in ['bootloops-lean','bootloops-lake']:
  p=subprocess.run([str(R/n),'--version'],cwd=O,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,timeout=30)
  (O/(n+'-version.log')).write_text(p.stdout);assert p.returncode==0
 fixtures={
 'FPCleanA':'import Std\ntheorem FPDetectorShared : True := True.intro\n',
 'FPCleanB':'import Std\ntheorem FPDetectorShared : True := True.intro\ntheorem FPDetectorOwn : (2:Nat)+3=5 := by decide\n',
 'FPHostile':'import Std\naxiom FPDetectorShared : True\ntheorem FPDetectorHostileOwn : (2:Nat)+3=5 := by decide\n',
 'FPPrivate':'import Std\nnamespace FPHidden\nprivate axiom unused : False\nprivate theorem ownClean : True := True.intro\nend FPHidden\n',
 'FPUnused':'import Std\naxiom FPUnusedPublic : True\ntheorem FPUnusedOwn : True := True.intro\n',
 'FPOpaqueClean':'import Std\nopaque FPOpaqueNumber : Nat := 7\nopaque FPOpaqueProof : True := True.intro\n',
 'FPOpaqueForeign':'import Std\naxiom FPOpaqueForeignAx : Nat\n',
 'FPOpaqueHostile':'import FPOpaqueForeign\nnoncomputable opaque FPOpaqueHostileBody : Nat := FPOpaqueForeignAx\n'}
 for n,s in fixtures.items():(O/(n+'.lean')).write_text(s);run(n,True)
 for i,mm in enumerate([['FPCleanA','FPCleanB'],['FPCleanB','FPCleanA']]):
  name='FPCleanAudit'+str(i);rows,_,_=audit_run(name,mm,set(fixtures))
  shared=[r for r in rows if r['name']=='FPDetectorShared'];assert len(shared)==2 and len({r['producer'] for r in shared})==2
  rec['controls'][name]=dict(shared_occurrences=2,total_occurrences=len(rows))
 for i,mm in enumerate([['FPCleanA','FPHostile'],['FPHostile','FPCleanA'],['FPPrivate'],['FPUnused']]):
  name='FPHostileAudit'+str(i);audit_run(name,mm,set(fixtures),1)
  with gzip.open(O/(name+'.log.gz'),'rt') as f:log=f.read()
  assert 'REJECT_DIRECT_CUSTOM_AXIOM|' in log
  rec['controls'][name]='CAUGHT_DIRECT_CUSTOM_AXIOM'
 rows,_,_=audit_run('FPOpaqueCleanAudit',['FPOpaqueClean'],set(fixtures));assert len([r for r in rows if r['kind']=='opaque' and r['body_sha256'] is not None])==2;rec['controls']['nonproof_opaque_bodies']='RETAINED_2_OF_2'
 audit_run('FPOpaqueHostileAudit',['FPOpaqueHostile'],set(fixtures),1)
 with gzip.open(O/'FPOpaqueHostileAudit.log.gz','rt') as f:assert 'REJECT_DEPENDENCY_CUSTOM_AXIOM|' in f.read()
 rec['controls']['opaque_body_axiom_walk']='CAUGHT'
 with gzip.open(O/'FPCleanAudit0.log.gz','rt') as f:cleanlog=f.read()
 first=re.search(r'^PRODUCERJSON\|.*$',cleanlog,re.M).group()
 for tag,bad in [('missing_row',cleanlog.replace(first+'\n','',1)),('duplicate_row',cleanlog+first+'\n'),
    ('foreign_path',cleanlog.replace('PATH|FPCleanA|'+str(O/'FPCleanA.olean'),'PATH|FPCleanA|/tmp/foreign/FPCleanA.olean',1))]:
  try:parse_lines(io.StringIO(bad),['FPCleanA','FPCleanB'],set(fixtures))
  except AssertionError:rec['controls'][tag]='CAUGHT'
  else:raise AssertionError('CORRUPTION_SURVIVED|'+tag)
 for tag,fn in [('source_pin',lambda:pin(R/entries[0]['path'],'0'*64)),
    ('adapted_bytes',lambda:adapted_pin((O/(mods[0]+'.lean')).read_text()+' ',entries[0]['adapted_sha256']))]:
  try:fn()
  except ValueError:rec['controls'][tag]='CAUGHT'
  else:raise AssertionError('CORRUPTION_SURVIVED|'+tag)
 (O/'FPStdTrue.lean').write_text('import Std\nexample : (2:Nat)+3=5 := by decide\n')
 (O/'FPStdFalse.lean').write_text('import Std\nexample : (2:Nat)+3=6 := by decide\n')
 run('FPStdTrue');p=run('FPStdFalse',want=1);assert p.stdout.count('is false')==1
 rec['controls']['known_true_false']='PASS_AND_REJECT';save()
 print('PASS_FRESH_STREAMING_PRODUCER_CONTROLS',flush=True)
 for n in mods:run(n,True);print('BUILT',n,flush=True)
 p=run('SelectorFalse',want=1);assert p.stdout.count('is false')==4
 rec['controls']['actual_false_math']='REJECTED_4_OF_4';save()
 allrows=[]
 for i,n in enumerate(mods):
  name='FPProducer'+str(i);rows,ss,paths=audit_run(name,[n],set(mods))
  allrows+=rows;rec['producer_audits'].append(dict(module=n,occurrences=len(rows),raw_gzip_sha256=sha(O/(name+'.log.gz'))));save()
  print('AUDITED',n,len(rows),flush=True)
 ax=sorted({a for row in allrows for a in row['axiom_references']});assert set(ax)<=A.ALLOW
 interfaces=['selected_literal_exists','buildSelected','buildSelected_complete','buildSelected_binding','selected_affordable_cover','selected_full_request_cover','selected_full_request_sound','full_state_paid_budget','rows_linear_bound']
 for key in interfaces:assert any(r['name']=='Universal233.Rule5PaidSelector.'+key for r in allrows),key
 (O/'producer-occurrences.json').write_text(json.dumps(allrows,indent=2)+'\n')
 for e in entries:pin(R/e['path'],e['sha256']);adapted_pin((O/(e['module']+'.lean')).read_text(),e['adapted_sha256'])
 for p,h in rec['input_hashes'].items():pin(R/p,h)
 for e in frozen:pin(R/e['path'],e['sha256'])
 limits();rec.update(status='PASS_AUTHOR_KERNEL_SOURCE_PRODUCER',source_builds=len(mods),stored_producer_occurrences=len(allrows),
  axiom_union=ax,interfaces=interfaces,skipped=['toolkit-wide suite','old AF census','fresh independent review','compiled machine semantics','parent dispatcher integration'],
  source_work='At most16 bottom rows per original source vertex proved; polynomial literal checks/bit/payload qualifications explicit; no recursive callback or compiled machine bill.')
 save();(O/'VERDICT.txt').write_text('PASS_AUTHOR_KERNEL_SOURCE_PRODUCER\nActual second selector to executable literal geometry and full paid current-forest requests; fresh review remains pending.\n')
 (D/'LATEST-REPLAY-v1.json').write_text(json.dumps(dict(receipt=str(O.relative_to(R)),certificate_sha256=sha(O/'certificate.json')),indent=2)+'\n')
 print('PASS_AUTHOR_KERNEL_SOURCE_PRODUCER',len(mods),len(allrows),ax,flush=True);print(O)
except BaseException as e:
 rec['status']='FAIL_RETAINED';rec['failure']=repr(e);save();print('FAIL_RETAINED',O,repr(e),flush=True);raise
