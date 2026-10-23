#!/usr/bin/env python3
"""New-module-only bounded replay on immutable source/olean hard links.
Prepared during a resource stop. Never launch below the live3GiB floor.
"""
from pathlib import Path
import datetime,gzip,hashlib,io,json,os,re,shutil,signal,subprocess,threading,time
D=Path(__file__).resolve().parent;R=D.parents[5]
FLOOR=3*1024**3;RAW=64*1024**2;LINE=16*1024**2;TOTAL=128*1024**2
TEMPLATE=R/'results/algorithm-universal233-ordinary-grouped-full-replay-20261015T194538090142Z/OBProducer0.lean'
ALLOW={'Classical.choice','Quot.sound','propext'}
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def pin(p,h):
 if sha(p)!=h:raise ValueError('SOURCE_OLEAN_PIN_MISMATCH|'+str(p))
def adapted_pin(s,h):
 if hashlib.sha256(s.encode()).hexdigest()!=h:raise ValueError('ADAPTED_BYTE_MISMATCH')
def source(mods):
 s=TEMPLATE.read_text();assert s.startswith('import FullStateJobs\n')
 s=s.replace('import FullStateJobs\n',''.join('import '+n+'\n' for n in mods),1)
 old='let expected : List Name := [`FullStateJobs]';new='let expected : List Name := ['+', '.join('`'+n for n in mods)+']'
 assert old in s;s=s.replace(old,new,1)
 assert 'ci.getUsedConstantsAsSet' in s and 'allowOpaque := true' in s and 'theorem_body_text_omitted' in s
 return s

def main():
 O=R/'results'/('algorithm-universal233-rule5-prefix-local-work-replay-'+datetime.datetime.now(datetime.timezone.utc).strftime('%Y%m%dT%H%M%S%fZ'));O.mkdir()
 rec=dict(status='RUNNING_AUTHOR',all_main_milestones='OPEN',novelty=False,independent_acceptance=False,improved_base=0,
  runtime_ghost=False,global_ordinary_IH=False,dependency_rebuilds=0,runs=[],controls={},producer_audits=[],
  body_qualification='All non-theorem/opaque bodies retained. Theorem proof text omitted only; actual full proof references and AX closures traversed.',
  disk_floor_bytes=FLOOR,directory_cap_bytes=TOTAL,module_timeout_seconds=30)
 def save():(O/'certificate.json').write_text(json.dumps(rec,indent=2)+'\n')
 def limits():
  free=shutil.disk_usage(O).free
  if free<FLOOR:raise RuntimeError('LIVE_DISK_FLOOR_3GIB|'+str(free))
  used=sum(p.stat().st_size for p in O.iterdir() if p.is_file())
  if used>TOTAL:raise RuntimeError('DIRECTORY_CAP|'+str(used))
  rec['resource_usage']=dict(free_bytes=free,logical_directory_bytes=used)
 deps=json.loads((D/'DEPENDENCIES.json').read_text());depmap={e['module']:e for e in deps}
 own=['PrefixScans','PrefixLeaves','ProperPairWork','CherryGuardWork','PrefixGuardEnvelope','PrefixWorkControls']
 local=set(depmap)|set(own)
 def dep_pins():
  for e in deps:
   p=R/e['source'];q=R/e['olean'];pin(p,e['source_sha256']);pin(q,e['olean_sha256'])
   assert os.path.samefile(O/(e['module']+'.lean'),p),'DEPENDENCY_SOURCE_LINK_CHANGED'
   assert os.path.samefile(O/(e['module']+'.olean'),q),'DEPENDENCY_OLEAN_LINK_CHANGED'
 def run(n,build=False,want=0,cap=RAW):
  limits();assert not build or n not in depmap,'REFUSE_REBUILD_LINKED_DEPENDENCY'
  start=time.monotonic();p=subprocess.Popen([str(R/'bootloops-lean')]+(['-o',str(O/(n+'.olean'))] if build else [])+[str(O/(n+'.lean'))],
   cwd=O,env=dict(os.environ,LEAN_PATH=str(O)),stdout=subprocess.PIPE,stderr=subprocess.STDOUT,start_new_session=True)
  stop=threading.Event();reason=[]
  def kill(why):
   reason.append(why)
   try:os.killpg(p.pid,signal.SIGTERM)
   except ProcessLookupError:pass
  def watch():
   while not stop.wait(0.1):
    if time.monotonic()-start>30:kill('PILOT_TIMEOUT_30S');return
    if shutil.disk_usage(O).free<FLOOR:kill('LIVE_DISK_FLOOR_3GIB');return
  monitor=threading.Thread(target=watch,daemon=True);monitor.start();count=0
  try:
   with gzip.open(O/(n+'.log.gz'),'wb') as z:
    while True:
     b=p.stdout.readline(LINE+1)
     if not b:break
     count+=len(b);z.write(b)
     if len(b)>LINE or count>cap:kill('OUTPUT_CAP');break
   code=p.wait(timeout=5)
  finally:stop.set();monitor.join()
  rec['runs'].append(dict(module=n,exit=code,seconds=time.monotonic()-start,raw_bytes=count,stop_reasons=reason));save()
  if reason:raise RuntimeError('|'.join(reason))
  assert code==want,(n,code)
  return O/(n+'.log.gz')
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
    rows.append({k:x[k] for k in ['producer','index','name','resolved_origin','kind','references','axiom_references']}|
      dict(type_sha256=hashlib.sha256(x['type'].encode()).hexdigest(),body_sha256=None if x['body'] is None else hashlib.sha256(x['body'].encode()).hexdigest()))
  assert len(summ)==len(mods) and {m for m,n in summ}==set(mods),'MISSING_OR_DUPLICATE_SUMMARY'
  assert seen=={(m,i) for m,n in summ for i in range(n)},'MISSING_ROW'
  assert set(mods)<=set(paths),'MISSING_PATH'
  for m,p in paths.items():
   p=Path(p).resolve()
   assert p==(O/(m+'.olean')).resolve() if m in allowed else p.is_relative_to(R/'.runtime/elan/toolchains'),'FOREIGN_PATH'
   if m in depmap:assert os.path.samefile(p,R/depmap[m]['olean']),'FOREIGN_DEPENDENCY_OLEAN'
  return rows,summ,paths
 def audit(n,mods,allowed,want=0):
  (O/(n+'.lean')).write_text(source(mods));log=run(n,want=want)
  if want:return log
  with gzip.open(log,'rt') as f:return parse(f,mods,allowed)
 try:
  limits()
  releases=[('research/rmaf/algorithm/universal233/ordinary_dispatch/rule5_local_work/FINAL-MANIFEST-v1.json','41824f76b9413353697301ec2c4a8672378a2c3a8cd1cc73d8a593a843aa9e8f')]
  rec['dependency_manifests']=[]
  for path,h in releases:
   M=R/path;pin(M,h);mf=json.loads(M.read_text())
   for e in mf['immutable_files']:pin(R/e['path'],e['sha256'])
   rec['dependency_manifests'].append(dict(path=path,sha256=h,immutable_files_verified=len(mf['immutable_files'])))
  rec['dependencies']=deps
  for e in deps:
   for sourcepath,n in [(R/e['source'],e['module']+'.lean'),(R/e['olean'],e['module']+'.olean')]:os.link(sourcepath,O/n)
  dep_pins();rec['audit_template']=dict(path=str(TEMPLATE.relative_to(R)),sha256=sha(TEMPLATE))
  rec['input_hashes']={str(p.relative_to(R)):sha(p) for p in D.iterdir() if p.is_file() and p.suffix in ['.lean','.md','.py','.json'] and p.name!='LATEST-REPLAY-v1.json'}
  for n in own+['PrefixWorkFalse']:(O/(n+'.lean')).write_bytes((D/(n+'.lean')).read_bytes())
  rec['source_entries']=[dict(module=n,path=str((D/(n+'.lean')).relative_to(R)),sha256=sha(D/(n+'.lean'))) for n in own]
  (O/'lean-toolchain').write_bytes((D/'build/lean-toolchain').read_bytes());save()
  fixtures={
   'OBCleanA':'import Std\ntheorem OBShared : True := True.intro\n',
   'OBCleanB':'import Std\ntheorem OBShared : True := True.intro\ntheorem OBOwn : (2:Nat)+3=5 := by decide\n',
   'OBHostile':'import Std\naxiom OBShared : True\ntheorem OBHostileOwn : True := True.intro\n',
   'OBPrivate':'import Std\nprivate axiom hidden : False\n',
   'OBUnused':'import Std\naxiom unused : True\ntheorem ownClean : True := True.intro\n',
   'OBOpaque':'import Std\nopaque OBNumber : Nat := 7\nopaque OBProof : True := True.intro\n',
   'OBForeign':'import Std\naxiom OBForeignAx : Nat\n',
   'OBOpaqueBad':'import OBForeign\nnoncomputable opaque OBBad : Nat := OBForeignAx\n'}
  allowed=local|set(fixtures)
  for n,s in fixtures.items():(O/(n+'.lean')).write_text(s);run(n,True)
  for i,mods in enumerate([['OBCleanA','OBCleanB'],['OBCleanB','OBCleanA']]):
   rows,_,_=audit('OBCleanAudit'+str(i),mods,allowed);assert len([r for r in rows if r['name']=='OBShared'])==2
   rec['controls']['clean_order'+str(i)]='PASS_TWO_STORED_PRODUCERS'
  for i,mods in enumerate([['OBCleanA','OBHostile'],['OBHostile','OBCleanA'],['OBPrivate'],['OBUnused']]):
   log=audit('OBHostileAudit'+str(i),mods,allowed,1)
   with gzip.open(log,'rt') as f:assert 'REJECT_DIRECT_CUSTOM_AXIOM|' in f.read()
   rec['controls']['hostile'+str(i)]='CAUGHT'
  rows,_,_=audit('OBOpaqueAudit',['OBOpaque'],allowed);assert len([r for r in rows if r['kind']=='opaque' and r['body_sha256']])==2
  rec['controls']['opaque_body_retention']='TWO_RETAINED'
  log=audit('OBOpaqueBadAudit',['OBOpaqueBad'],allowed,1)
  with gzip.open(log,'rt') as f:assert 'REJECT_DEPENDENCY_CUSTOM_AXIOM|' in f.read()
  rec['controls']['opaque_AXIOM_walk']='CAUGHT'
  with gzip.open(O/'OBCleanAudit0.log.gz','rt') as f:clean=f.read()
  first=re.search(r'^PRODUCERJSON\|.*$',clean,re.M).group()
  for tag,bad in [('missing_row',clean.replace(first+'\n','',1)),('duplicate_row',clean+first+'\n'),('foreign_path',clean.replace('PATH|OBCleanA|'+str(O/'OBCleanA.olean'),'PATH|OBCleanA|/tmp/foreign/OBCleanA.olean',1))]:
   try:parse(io.StringIO(bad),['OBCleanA','OBCleanB'],allowed)
   except AssertionError:rec['controls'][tag]='CAUGHT'
   else:raise AssertionError('CORRUPTION_SURVIVED|'+tag)
  for tag,fn in [('dependency_source',lambda:pin(R/deps[0]['source'],'0'*64)),('dependency_olean',lambda:pin(R/deps[0]['olean'],'0'*64)),('adapted_bytes',lambda:adapted_pin((D/'PrefixScans.lean').read_text()+' ',sha(D/'PrefixScans.lean')))]:
   try:fn()
   except ValueError:rec['controls'][tag]='CAUGHT'
   else:raise AssertionError('CORRUPTION_SURVIVED|'+tag)
  (O/'OBTrue.lean').write_text('import Std\nexample : (2:Nat)+3=5 := by decide\n');run('OBTrue')
  (O/'OBFalse.lean').write_text('import Std\nexample : (2:Nat)+3=6 := by decide\n');log=run('OBFalse',want=1)
  with gzip.open(log,'rt') as f:assert f.read().count('is false')==1
  rec['controls']['true_false']='PASS_REJECT';save();print('PASS_FRESH_NEW_MODULE_AUDIT_CONTROLS',flush=True)
  for n in own:
   log=run(n,True);print('BUILT_NEW_ONLY',n,flush=True)
   if n=='PrefixWorkControls':
    with gzip.open(log,'rt') as f:out=f.read()
    assert '("PASS_LITERAL_PREFIX_WORK_CONTROLS", true)' in out,'RUNTIME_TRUTH_CONTROLS_FAILED'
    assert 'false' not in out,'RUNTIME_FALSE_BOOLEAN'
    expected=['equal','permuted','unequal','repeated','asymmetric','empty_member','early_hit','late_hit','missing','tail_first_duplicate','distinct_nodup','same_boolean_missing_scan','cherry_both_orders','cherry_miss','leaf_no_cherry','malformed_refuses','leaves_payload']
    for name in expected:assert '("'+name+'", true)' in out,('MISSING_RUNTIME_CONTROL',name)
    rec['controls']['actual_runtime']='SEVENTEEN_PASS_ACTUAL_PREFIX_BODY_FIXTURES';save()
  log=run('PrefixWorkFalse',want=1)
  with gzip.open(log,'rt') as f:assert f.read().count('is false')==4
  rec['controls']['false_math']='FOUR_REJECTED';save()
  allrows=[]
  for i,n in enumerate(own):
   rows,summary,paths=audit('OBProducer'+str(i),[n],allowed);allrows+=rows;rec['producer_audits'].append(dict(module=n,occurrences=len(rows)));save();print('AUDITED_NEW_ONLY',n,len(rows),flush=True)
  required=['containsMeter','contains_value','contains_work','missing_contains_work','nodupMeter','nodup_value','nodup_work','allContainsMeter','all_contains_value','all_contains_work','leavesMeter','leaves_value','leaves_work','properPairMeter','proper_pair_value','proper_pair_split','properPolynomial','proper_pair_work','cherriesMeter','cherries_value','cherries_count','cherries_work','hasCherryMeter','has_cherry_value','has_cherry_work','cherry_row_payload','guardPrefixMeter','guard_prefix_value','admitted_has_prefix','prefix_false_refuses','guard_prefix_work','leaf_payload_domain','cherry_payload_domain','guard_prefix_scaled']
  for key in required:assert any(r['name']=='Universal233.Rule5PrefixLocalWork.'+key for r in allrows),key
  with gzip.open(O/'producer-occurrences.json.gz','wt') as f:json.dump(allrows,f,separators=(',',':'))
  dep_pins()
  for p,h in rec['input_hashes'].items():pin(R/p,h)
  limits();rec.update(status='PASS_AUTHOR_NEW_SOURCE_OLEAN_PRODUCER_BOUND',new_source_builds=len(own),dependency_source_olean_pairs=len(deps),new_stored_producer_occurrences=len(allrows),axiom_union=sorted({a for r in allrows for a in r['axiom_references']}),interfaces=required)
  save();(O/'VERDICT.txt').write_text('PASS_AUTHOR_NEW_SOURCE_OLEAN_PRODUCER_BOUND\nSTAGE ONLY: actual properPair and hasCherry source-body companions and structural polynomial; raw refused/duplicate inputs covered. admitted pendantPartition/candidate construction and full source-bit/base/main claims OPEN.\n')
  (D/'LATEST-REPLAY-v1.json').write_text(json.dumps(dict(receipt=str(O.relative_to(R)),sha256=sha(O/'certificate.json')),indent=2)+'\n')
  print('PASS_AUTHOR_NEW_SOURCE_OLEAN_PRODUCER_BOUND',len(own),len(deps),len(allrows),rec['axiom_union'],O,flush=True)
 except BaseException as e:
  rec['status']='RESOURCE_STOP_RETAINED' if 'FLOOR' in str(e) else 'FAIL_RETAINED';rec['failure']=repr(e);save();print(rec['status'],O,repr(e),flush=True);raise

if __name__=='__main__':main()
