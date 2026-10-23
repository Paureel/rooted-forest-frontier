#!/usr/bin/env python3
"""One-shot bounded lossless sink wrapper, completed author extractors reused.
Preserves interrupted raw output; extracts only missing producer modules.
"""
from pathlib import Path
import datetime,gzip,hashlib,importlib.util,json,os,re,resource,selectors,shlex,shutil,signal,subprocess,time
D=Path(__file__).resolve().parent;R=D.parents[5]
B=R/'results/algorithm-universal233-ordinary-source-pool-20261015T144445575127Z'
P=R/'results/algorithm-universal233-ordinary-source-pool-resume-20261015T181255871989Z'
O=R/'results'/('algorithm-universal233-ordinary-source-pool-compressed-'+datetime.datetime.now(datetime.timezone.utc).strftime('%Y%m%dT%H%M%S%fZ'));O.mkdir()
def load(name,p):
 s=importlib.util.spec_from_file_location(name,p);m=importlib.util.module_from_spec(s);s.loader.exec_module(m);return m
A=load('compressed_completed_split',R/'research/rmaf/algorithm/universal233/rule5_common_split/audit_graph.py')
C=load('compressed_completed_controls',R/'research/rmaf/algorithm/universal233/rule5_case322/audit.py')
G=load('compressed_completed_values',D.parent/'producer_compatibility/compatibility.py')
def sha(p):
 h=hashlib.sha256()
 with p.open('rb') as f:
  for b in iter(lambda:f.read(1<<20),b''):h.update(b)
 return h.hexdigest()
def string_sha(s):
 h=hashlib.sha256()
 for i in range(0,len(s),1<<20):h.update(s[i:i+(1<<20)].encode())
 return h.hexdigest()
def pin(data,h):assert hashlib.sha256(data).hexdigest()==h,'PIN_MISMATCH'
rec=dict(status='FRESH_COMPRESSED_CONTROLS',all_main_milestones='OPEN',independent_acceptance=False,full_algorithm=False,runtime_claim=False,runs=[],controls={},saved_producers=[],new_producers=[],inputs={})
for p in [Path(__file__),D/'COMPRESSED-AUDIT-AMENDMENT-v1.md',Path(A.__file__),Path(C.__file__),Path(G.__file__),B/'construction.json',P/'certificate.json']:
 rec['inputs'][str(p.relative_to(R))]=sha(p)
def save():(O/'certificate.json').write_text(json.dumps(rec,indent=2)+'\n')
def margin():assert shutil.disk_usage(R).free>=3*(1<<30),'FREE_SPACE_MARGIN_STOP'
def cap():resource.setrlimit(resource.RLIMIT_FSIZE,(512*(1<<20),512*(1<<20)))
def run(root,name,pathroot,build=False,want=0):
 margin();start=time.monotonic();p=subprocess.Popen([str(R/'bootloops-lean')]+(['-o',str(root/(name+'.olean'))] if build else [])+[str(root/(name+'.lean'))],cwd=root,env=dict(os.environ,LEAN_PATH=str(pathroot)),stdout=subprocess.PIPE,stderr=subprocess.STDOUT,preexec_fn=cap,start_new_session=True)
 chunks=[];size=0;failure=None;sel=selectors.DefaultSelector();sel.register(p.stdout,selectors.EVENT_READ)
 try:
  while sel.get_map():
   if time.monotonic()-start>60:failure='COMMAND_60S_CAP'
   elif shutil.disk_usage(R).free<3*(1<<30):failure='FREE_SPACE_MARGIN_STOP'
   elif size>8*(1<<20):failure='METADATA_STDOUT_8MIB_CAP'
   if failure:
    os.killpg(p.pid,signal.SIGINT);break
   for key,ev in sel.select(0.25):
    b=os.read(key.fd,1<<16)
    if b:chunks.append(b);size+=len(b)
    else:sel.unregister(key.fileobj)
  try:tail=p.communicate(timeout=3)[0]
  except subprocess.TimeoutExpired:os.killpg(p.pid,signal.SIGKILL);tail=p.communicate()[0]
  if tail:chunks.append(tail)
 finally:sel.close()
 output=b''.join(chunks).decode(errors='replace');(root/(name+'.log')).write_text(output)
 rec['runs'].append(dict(module=name,exit=p.returncode,seconds=time.monotonic()-start,stdout_bytes=size,resource_stop=failure));save()
 assert failure is None,failure
 assert p.returncode==want,(name,output[-5000:]);return output

def source(imports,wanted,out):
 s=A.audit_source(imports,wanted,out)
 s=s.replace('producer.toString ++ ".json"','producer.toString ++ ".json.gz"')
 old='      liftIO <| IO.FS.writeFile ('+json.dumps(str(out))+' ++ "/" ++ filename) (Json.arr rows).pretty'
 command='exec /usr/bin/gzip -1 -c > '+shlex.quote(str(out))+'/'
 new='      let compressed ← liftIO <| IO.Process.output {cmd := "/bin/sh", args := #["-c", '+json.dumps(command)+' ++ filename]} (some (Json.arr rows).pretty)\n      unless compressed.exitCode == 0 do throwError "COMPRESSED_SINK_FAILED"'
 assert s.count(old)==1;s=s.replace(old,new)
 return s

def header_source(imports):
 return '\n'.join('import '+n for n in imports)+'''\nimport Lean
open Lean Elab Command
run_cmd do
 let env ← getEnv
 let wanted : List Name := ['''+', '.join('`'+n for n in imports)+''']
 for i in [:env.header.moduleNames.size] do
  let producer := env.header.moduleNames[i]!
  let path ← liftIO <| findOLean producer
  logInfo m!"PATH|{producer}|{path}"
  if wanted.contains producer then
   let data := env.header.moduleData[i]!
   unless data.constants.size == data.constNames.size do throwError "HEADER_ARRAY_MISMATCH"
   logInfo m!"COUNT|{producer}|{data.constants.size}"
   for j in [:data.constants.size] do
    let ci := data.constants[j]!
    let kind := match ci with
      | .axiomInfo _ => "axiom" | .defnInfo _ => "definition" | .thmInfo _ => "theorem"
      | .opaqueInfo _ => "opaque" | .quotInfo _ => "quotient" | .ctorInfo _ => "constructor"
      | .recInfo _ => "recursor" | .inductInfo _ => "inductive"
    logInfo m!"NAME|{producer}|{j}|{ci.name}|{kind}"
'''
def parse_header(log,names,root):
 pairs=re.findall(r'^PATH\|([^|]+)\|(.+)$',log,re.M);paths=dict(pairs);assert len(paths)==len(pairs)
 assert set(names)<=set(paths)
 for n,p in paths.items():
  q=Path(p).resolve();assert q==(root/(n+'.olean')).resolve() if n in names else q.is_relative_to(R/'.runtime/elan/toolchains'),'FOREIGN_MODULE_PATH'
 counts=dict((n,int(c)) for n,c in re.findall(r'^COUNT\|([^|]+)\|(\d+)$',log,re.M));assert set(counts)==set(names)
 rows={n:[] for n in names}
 for n,i,x,k in re.findall(r'^NAME\|([^|]+)\|(\d+)\|([^|]+)\|([^\n]+)$',log,re.M):rows[n].append((int(i),x,k))
 for n in names:assert len(rows[n])==counts[n] and [x[0] for x in rows[n]]==list(range(counts[n]))
 return counts,rows

def extract(root,imports,wanted,pathroot,label,want=0):
 out=root/('records-'+label);out.mkdir();name='Compressed'+label
 (root/(name+'.lean')).write_text(source(imports,wanted,out));run(root,name,pathroot,want=want)
 idx=json.loads((out/'index.json').read_text());assert len(idx['producer_counts'])==len(wanted) and {x['producer'] for x in idx['producer_counts']}==set(wanted)
 return idx,out

def read_rows(path):
 assert path.stat().st_size<(1<<30),'SAVED_PRODUCER_FILE_CAP'
 with (gzip.open(path,'rt') if path.suffix=='.gz' else path.open()) as f:rows=json.load(f)
 return rows

def fingerprint(rows):
 result=[]
 for r in rows:
  z=dict(r);z['type']='sha256:'+string_sha(z['type']);z['body']='sha256:'+string_sha(z['body']);result.append(z)
 return result
save();(O/'lean-toolchain').write_bytes((B/'lean-toolchain').read_bytes())
try:
 T=O/'controls';T.mkdir();(T/'lean-toolchain').write_bytes((B/'lean-toolchain').read_bytes())
 # The exact new sink, including direct and coalesced custom axioms, is controlled first.
 fixtures={'ZipCleanA':'theorem ZipShared : True := True.intro\n','ZipCleanB':'theorem ZipShared : True := True.intro\ntheorem ZipOwn : True := True.intro\n','ZipHostile':'axiom ZipShared : True\ntheorem ZipHostileOwn : True := True.intro\n','ZipPrivate':'namespace ZipHidden\nprivate axiom unused : False\nend ZipHidden\n','ZipUnused':'axiom ZipUnusedPublic : True\n','ZipZero':'namespace ZipValue\ndef value : Nat := 0\nend ZipValue\n','ZipOne':'namespace ZipValue\ndef value : Nat := 1\nend ZipValue\n','ZipTwin':'namespace ZipValue\ndef value : Nat := 0\nend ZipValue\n'}
 for n,s in fixtures.items():(T/(n+'.lean')).write_text('import Std\n'+s);run(T,n,T,build=True)
 cleanrows=None
 for i,imports in enumerate([['ZipCleanA','ZipCleanB'],['ZipCleanB','ZipCleanA'],['ZipHostile','ZipCleanA'],['ZipCleanA','ZipHostile'],['ZipPrivate'],['ZipUnused']]):
  hostile=i>=2;idx,out=extract(T,imports,imports,T,'Control'+str(i),want=int(hostile));bad=[];rr=[]
  for count in idx['producer_counts']:
   rows=read_rows(out/count['file']);bad.extend(A.parse_producer(count,rows,expect_reject=hostile));rr.extend(rows)
  assert bool(bad)==hostile
  if not hostile:assert len([r for r in rr if r['actual_name']=='ZipShared'])==2
  rec['controls']['sink'+str(i)]=dict(hostile=hostile,detected=bool(bad),rows=len(rr))
  if i==0:cleanrows=(idx['producer_counts'][0],read_rows(out/idx['producer_counts'][0]['file']))
 vv={}
 for n in ['ZipZero','ZipOne','ZipTwin']:
  idx,out=extract(T,[n],[n],T,n);rr=read_rows(out/idx['producer_counts'][0]['file']);vv[n]=[r for r in fingerprint(rr) if r['actual_name']=='ZipValue.value'];assert len(vv[n])==1
 for label,ns,want in [('clean_value',['ZipZero','ZipTwin'],False),('bad_LR',['ZipZero','ZipOne'],True),('bad_RL',['ZipOne','ZipZero'],True)]:
  answer=G.inspect([r for n in ns for r in vv[n]]);assert bool(answer['rejects'])==want;rec['controls'][label]=answer
 count,rr=cleanrows
 for label,bad in [('missing',rr[:-1]),('duplicate',rr+[rr[0]]),('foreign_producer',[dict(r,producer='Foreign') if i==0 else r for i,r in enumerate(rr)]),('custom_reference',[dict(r,axiom_references=['Forbidden']) if i==0 else r for i,r in enumerate(rr)])]:
  try:A.parse_producer(count,bad)
  except AssertionError:rec['controls'][label]='CAUGHT'
  else:raise AssertionError('CORRUPTION_SURVIVED|'+label)
 empty='e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855';pin(b'',empty)
 try:pin(b'x',empty)
 except AssertionError:rec['controls']['production_pin_corruption']='CAUGHT'
 else:raise AssertionError('CORRUPTION_SURVIVED|pin')
 (T/'FalseProof.lean').write_text('import Std\nexample : (2:Nat)+3=6 := by decide\n');run(T,'FalseProof',T,want=1)
 rec['controls']['false_proof']='REJECTED';rec['status']='FRESH_COMPRESSED_CONTROLS_PASS';save()
 old=json.loads((B/'construction.json').read_text());names=[x['module'] for x in old['source_modules']];assert len(names)==306
 oldpins=json.loads((P/'OLD-BUILD-PINS.json').read_text())
 for p,h in oldpins.items():assert sha(R/p)==h,'OLD_BUILD_CHANGED'
 (O/'FreshHeader.lean').write_text(header_source(names));log=run(O,'FreshHeader',B);counts,expected=parse_header(log,names,B)
 for label,bad in [('foreign_path',log.replace(str(B/'RMAF.olean'),'/tmp/foreign/RMAF.olean',1)),('missing_path',re.sub(r'^PATH\|RMAF\|.*\n','',log,flags=re.M))]:
  try:parse_header(bad,names,B)
  except AssertionError:rec['controls'][label]='CAUGHT'
  else:raise AssertionError('CORRUPTION_SURVIVED|'+label)
 allrows=[];missing=[]
 for n in names:
  options=list(P.glob('records-Shard*/'+n+'.json'))
  assert len(options)<=1
  if not options:missing.append(n);continue
  p=options[0];rr=read_rows(p);A.parse_producer(dict(producer=n,count=counts[n]),rr)
  assert [(r['index'],r['actual_name'],r['kind']) for r in rr]==expected[n],'FRESH_HEADER_MISMATCH'
  allrows.extend(fingerprint(rr));rec['saved_producers'].append(dict(module=n,path=str(p.relative_to(R)),sha256=sha(p),occurrences=len(rr)));del rr
  save()
  if len(rec['saved_producers'])%20==0:print('SAVED_VALIDATED',len(rec['saved_producers']),flush=True)
 rec.update(status='MISSING_ONLY_COMPRESSED_EXTRACTION',missing_modules=missing);save();total=0
 for i,n in enumerate(missing):
  margin();idx,out=extract(O,names,[n],B,'Actual'+str(i));assert not idx['rejects'];count=idx['producer_counts'][0];p=out/count['file'];total+=p.stat().st_size
  assert total<=768*(1<<20),'TOTAL_COMPRESSED_OUTPUT_CAP'
  rr=read_rows(p);A.parse_producer(count,rr);assert [(r['index'],r['actual_name'],r['kind']) for r in rr]==expected[n]
  allrows.extend(fingerprint(rr));rec['new_producers'].append(dict(module=n,path=str(p.relative_to(R)),sha256=sha(p),compressed_bytes=p.stat().st_size,occurrences=len(rr)));del rr;save()
  print('NEW_COMPRESSED',i+1,'OF',len(missing),n,'BYTES',total,flush=True)
 result=G.inspect(allrows);(O/'PRODUCER-COMPATIBILITY-v1.json').write_text(json.dumps(result,indent=2)+'\n');assert not result['rejects'],result['rejects']
 assert len(rec['saved_producers'])+len(rec['new_producers'])==306
 for p,h in rec['inputs'].items():assert sha(R/p)==h,'INPUT_CHANGED'
 for p,h in oldpins.items():assert sha(R/p)==h,'OLD_BUILD_CHANGED'
 axs=sorted({a for r in allrows for a in r['axiom_references']});assert set(axs)<=A.ALLOWED
 rec.update(status='PASS_AUTHOR_COMPRESSED_POOL_AUDIT',source_modules=306,stored_producer_occurrences=len(allrows),unique_names=len({r['actual_name'] for r in allrows}),axiom_union=axs,duplicate_groups=len(result['duplicates']),compressed_bytes=total,source_build_claim='Continued prior306sourcebuilds; no new individual rebuild. Exact source/log/olean pins checked before/after; fresh all306master header binds every producer index/name/kind and modulepath; every fullstoredrow retained raw or gzip; type/body compatibility is SHA256 of exact representation strings.',global_claims='Algorithm/correctness/base/novelty OPEN; author integration only')
 save();(O/'VERDICT.txt').write_text(rec['status']+'\nAll main claims OPEN; independent acceptance false.\n');print(rec['status'],len(allrows),flush=True)
except BaseException as e:rec.update(status='FAILED_NOT_ACCEPTED',error=repr(e));save();raise
finally:(D/'LATEST-COMPRESSED-POOL-v1.json').write_text(json.dumps(dict(directory=str(O.relative_to(R)),certificate_sha256=sha(O/'certificate.json')),indent=2)+'\n')
