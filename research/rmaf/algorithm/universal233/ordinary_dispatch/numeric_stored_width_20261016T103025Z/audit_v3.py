# One-shot local full-body audit adapter. Existing extractor and parser unchanged.
from pathlib import Path
import ast,datetime,gzip,hashlib,importlib.util,json,os,re,resource,selectors,shlex,shutil,signal,subprocess,time
D=Path(__file__).resolve().parent;R=D.parents[5]
P=json.loads((D/'DEPENDENCY-PINS-v3.json').read_text());B=R/P['pool'];O=D/'author-audit-v3';O.mkdir()
V=R/'research/rmaf/algorithm/universal233/ordinary_dispatch/resume_20261015T1810Z/compressed_pool_resume_v3.py'
assert hashlib.sha256(V.read_bytes()).hexdigest()=='626e3f21ba70fb417ad1085995a88b4af217a1b6f210191fa58ca442aad0098a'
def load(n,p):
 spec=importlib.util.spec_from_file_location(n,p);m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m);return m
A=load('numeric_audit_parser',R/'research/rmaf/algorithm/universal233/rule5_common_split/audit_graph.py')
for n in ast.parse(V.read_text()).body:
 if isinstance(n,ast.FunctionDef) and n.name in {'sha','string_sha','source','header_source'}:
  exec(compile(ast.Module(body=[n],type_ignores=[]),str(V),'exec'),globals())
qualified_source=source
def source(imports,modules,out):
 s=qualified_source(imports,modules,out)
 if not set(modules)<={'StoredPrecontrols','StoredMax','NumericAuditClean','NumericAuditHostile'}:return s
 a='let body := match ci with | .thmInfo _ => none | _ => ci.value? true';assert s.count(a)==1
 s=s.replace(a,'let body := ci.value? true')
 a='match ci with | .thmInfo _ => "OMITTED_THEOREM_PROOF_TEXT" | _ => "FULL_NONPROOF_BODY"';assert s.count(a)==1
 return s.replace(a,'"FULL_ALL_BODY"')
rec=dict(status='CHECKING',same_author=True,independent_credit=0,full233=False,native=False,novelty=False,runs=[],controls={},inputs={},sources=[],new_producers=[],inherited_audit_qualification='Frozen imported records remain at their existing qualifications; exact chosen source/object closure matched. No blanket re-extraction of imported full bodies.')
def save():(O/'certificate.json').write_text(json.dumps(rec,indent=2)+'\n')
def run(root,name,pathroot,build=False,want=0):
 assert shutil.disk_usage(D).free>=3*(1<<30)
 start=time.monotonic();cmd=[str(R/'bootloops-lean'),'--memory=3072']+(['-o',str(root/(name+'.olean'))] if build else [])+[str(root/(name+'.lean'))]
 def limit():resource.setrlimit(resource.RLIMIT_FSIZE,(16*(1<<20),16*(1<<20)))
 p=subprocess.Popen(cmd,cwd=root,env=dict(os.environ,LEAN_PATH=str(pathroot)),stdout=subprocess.PIPE,stderr=subprocess.STDOUT,preexec_fn=limit,start_new_session=True)
 size=0;chunks=[];failure=None;sel=selectors.DefaultSelector();sel.register(p.stdout,selectors.EVENT_READ)
 while sel.get_map():
  if time.monotonic()-start>30:failure='30S_PILOT_CAP'
  if size>4*(1<<20):failure='4MIB_STDOUT_CAP'
  if shutil.disk_usage(D).free<3*(1<<30):failure='3GIB_DISK_FLOOR'
  if failure:os.killpg(p.pid,signal.SIGTERM);break
  for key,event in sel.select(0.2):
   buf=os.read(key.fd,1<<16)
   if buf:chunks.append(buf);size+=len(buf)
   else:sel.unregister(key.fileobj)
 try:tail=p.communicate(timeout=3)[0]
 except subprocess.TimeoutExpired:os.killpg(p.pid,signal.SIGKILL);tail=p.communicate()[0]
 sel.close();chunks.append(tail);out=b''.join(chunks);(root/(name+'.log')).write_bytes(out)
 rec['runs'].append(dict(module=name,exit=p.returncode,expected=want,seconds=time.monotonic()-start,stdout_bytes=len(out),resource_stop=failure));save()
 assert failure is None and p.returncode==want,(name,failure,p.returncode,out[-1500:])
 assert b'declaration uses `sorry`' not in out
 return out.decode()
def extract(label,imports,mods,pathroot,want=0):
 folder=O/('records-'+label);folder.mkdir();name='Body'+label
 (O/(name+'.lean')).write_text(source(imports,mods,folder));run(O,name,pathroot,want=want)
 idx=json.loads((folder/'index.json').read_text());assert len(idx['producer_counts'])==len(mods)
 assert {r['producer'] for r in idx['producer_counts']}==set(mods)
 result=[]
 for c in idx['producer_counts']:
  f=folder/c['file'];assert f.stat().st_size<=16*(1<<20),'16MIB_COMPRESSED_CAP'
  with gzip.open(f,'rb') as stream:raw=stream.read(256*(1<<20)+1)
  assert len(raw)<=256*(1<<20),'256MIB_RAW_CAP'
  assert max(map(len,raw.splitlines()),default=0)<=128*(1<<20),'128MIB_LINE_CAP'
  rows=json.loads(raw);bad=A.parse_producer(c,rows,expect_reject=bool(want));assert bool(bad)==bool(want)
  expected_full=c['producer'] in {'StoredPrecontrols','StoredMax','NumericAuditClean','NumericAuditHostile'}
  assert all(r['body_text_scope']==('FULL_ALL_BODY' if expected_full or r['kind']!='theorem' else 'OMITTED_THEOREM_PROOF_TEXT') or (not expected_full and r['kind']!='theorem' and r['body_text_scope']=='FULL_NONPROOF_BODY') for r in rows)
  assert all(r['has_body'] and r['body']!='<none>' for r in rows if r['kind'] in {'definition','opaque'} or (expected_full and r['kind']=='theorem'))
  result.append((c,f,rows,len(raw)))
 return idx,result
save();(O/'lean-toolchain').write_bytes((D/'lean-toolchain').read_bytes())
try:
 for p in [V,Path(A.__file__),Path(__file__),D/'DEPENDENCY-PINS-v1.json',D/'DEPENDENCY-PINS-v2.json',D/'DEPENDENCY-PINS-v3.json',D/'CONTROLS-v1.json',D/'CONTROLS-v2.json',D/'CONTROL-DIAGNOSIS-v3.json',D/'compile_v1.py',D/'AUDIT-QUALIFICATION-v2.json',D/'author-audit-v1/certificate.json',D/'author-audit-v2/certificate.json']:
  rec['inputs'][str(p.relative_to(R))]=sha(p)
 oldfile=B/'receipt.json';assert sha(oldfile)=='74ab9988f529127eb4d01516d225540c996e0ec53efee63c4d55cfdbe75b769c'
 old=json.loads(oldfile.read_text());rec['inputs'][str(oldfile.relative_to(R))]=sha(oldfile)
 manifest=R/P['manifest']['manifest'];assert sha(manifest)==P['manifest']['sha256']
 m=json.loads(manifest.read_text());oldpins={x['path']:x for x in m['immutable_files']}
 for row in P['files']:
  f=R/row['path'];s=f.stat();assert (sha(f),s.st_size,s.st_ino,s.st_dev,s.st_mode&0o777)==(row['sha256'],row['bytes'],row['inode'],row['device'],row['mode'])
  assert row['sha256']==oldpins[row['path']]['sha256']
 rec['inherited_exact_modules']=len(P['modules']);save()
 # Fresh clean/hostile controls through the same full-body sink.
 C=O/'controls';C.mkdir();(C/'lean-toolchain').write_bytes((D/'lean-toolchain').read_bytes())
 fixtures={'NumericAuditClean':'import Std\ndef numericAuditValue : Nat := 0\ntheorem numericAuditKnown : (2:Nat)+3=5 := by decide\n',
 'NumericAuditHostile':'import Std\naxiom numericForbidden : True\ntheorem numericForeignProof : True := numericForbidden\n'}
 for n,s in fixtures.items():(C/(n+'.lean')).write_text(s);run(C,n,C,build=True)
 cleanidx,clean=extract('Clean',['NumericAuditClean'],['NumericAuditClean'],C)
 assert not cleanidx['rejects'];rec['controls']['clean_full_body']='PASS'
 badidx,bad=extract('Hostile',['NumericAuditHostile'],['NumericAuditHostile'],C,want=1)
 assert badidx['rejects'] and any(r['actual_name']=='numericForeignProof' and 'numericForbidden' in r['axiom_references'] for r in bad[0][2])
 rec['controls']['forbidden_axiom_and_actual_proof_body_walk']='CAUGHT'
 count,_,rows,_=clean[0]
 for label,mut in [('missing',rows[:-1]),('duplicate',rows+[rows[0]]),('axiom_reference',[dict(r,axiom_references=['Forbidden']) if i==0 else r for i,r in enumerate(rows)])]:
  try:A.parse_producer(count,mut)
  except AssertionError:rec['controls'][label]='CAUGHT'
  else:raise AssertionError('CONTROL_SURVIVED '+label)
 save()
 own=['StoredPrecontrols','StoredMax','StoredFreshPair','StoredRelabel','StoredContract','StoredCommonPayload','StoredTransport','StoredPolicy','StoredBudget','StoredSourceSite','StoredControls','StoredSourceControls','StoredOrientations','StoredOrientedControls']
 seen=set();order=[]
 def visit(n):
  if n in seen:return
  p=(D if n in own else B)/(n+'.lean');o=p.with_suffix('.olean');assert p.exists() and o.exists(),n
  for dep in re.findall(r'^import ([A-Za-z0-9_\'.]+)\s*$',p.read_text(),re.M):
   if dep.split('.')[0] not in {'Std','Lean','Init'}:visit(dep)
  seen.add(n);order.append(n);rec['sources'].append(dict(module=n,source=str(p.relative_to(R)),source_sha256=sha(p),olean=str(o.relative_to(R)),olean_sha256=sha(o),owned=n in own))
 visit('StoredOrientedControls');assert set(order)==set(P['modules'])|set(own)
 compile_records=[]
 for file in (D/'attempts').glob('*/receipt.json'):
  value=json.loads(file.read_text())
  if value.get('accepted') and value.get('exit')==0 and value.get('expected')==0 and value.get('olean_sha256'):
   compile_records.append((file,value))
 rec['current_compile_bindings']=[]
 for n in own:
  candidates=[(file,value) for file,value in compile_records if value['module']==n and value['source_sha256']==sha(D/(n+'.lean')) and value['olean_sha256']==sha(D/(n+'.olean'))]
  assert candidates,('NO_CURRENT_SOURCE_OBJECT_COMPILE_RECEIPT',n)
  file,value=candidates[-1];rec['current_compile_bindings'].append(dict(module=n,receipt=str(file.relative_to(R)),sha256=sha(file)))
 save()
 (O/'Header.lean').write_text(header_source(own));header=run(O,'Header',str(D)+os.pathsep+str(B))
 paths=dict(re.findall(r'^PATH\|([^|]+)\|(.+)$',header,re.M));assert set(order)<=set(paths)
 for n,p in paths.items():
  f=Path(p).resolve()
  if n in own:assert f==(D/(n+'.olean')).resolve()
  elif n in P['modules']:assert f==(B/(n+'.olean')).resolve()
  else:assert f.is_relative_to(R/'.runtime/elan/toolchains')
 counts={n:int(c) for n,c in re.findall(r'^COUNT\|([^|]+)\|(\d+)$',header,re.M)};assert set(counts)==set(own)
 expected={n:[] for n in own}
 for n,i,x,k in re.findall(r'^NAME\|([^|]+)\|(\d+)\|([^|]+)\|([^\n]+)$',header,re.M):expected[n].append((int(i),x,k))
 for n in own:assert len(expected[n])==counts[n]
 total=0;axioms=set();stored=0;runtime_rows={}
 for i,n in enumerate(own):
  prior=json.loads((D/'author-audit-v2/certificate.json').read_text());entries={e['module']:e for e in prior['new_producers']};olds={e['module']:e for e in prior['sources']}
  if n in entries:
   e=entries[n];oldsource=olds[n];assert sha(D/(n+'.lean'))==oldsource['source_sha256'] and sha(D/(n+'.olean'))==oldsource['olean_sha256']
   f=R/e['path'];assert sha(f)==e['sha256']
   with gzip.open(f,'rb') as stream:body=stream.read(256*(1<<20)+1)
   assert len(body)<=256*(1<<20);rows=json.loads(body);raw=len(body);c=dict(producer=n,count=e['stored_occurrences']);A.parse_producer(c,rows)
  else:
   idx,rs=extract('Own'+str(i),['StoredOrientedControls'],[n],str(D)+os.pathsep+str(B));assert not idx['rejects']
   c,f,rows,raw=rs[0]
  assert [(r['index'],r['actual_name'],r['kind']) for r in rows]==expected[n]
  assert all(r['resolved_origin']==n for r in rows),'SHADOWED_NEW_DECLARATION'
  for row in rows:
   axioms.update(row['axiom_references']);runtime_rows[row['actual_name']]=dict(kind=row['kind'],references=row['direct_references'])
  total+=f.stat().st_size;assert total<=128*(1<<20),'128MIB_NEW_AGGREGATE_CAP';stored+=len(rows)
  rec['new_producers'].append(dict(module=n,path=str(f.relative_to(R)),sha256=sha(f),stored_occurrences=len(rows),compressed_bytes=f.stat().st_size,raw_bytes=raw,full_all_bodies=n in {'StoredPrecontrols','StoredMax'},full_nonproof_bodies=True,actual_full_proof_reference_axiom_walk=True));save();print('AUDITED',n,len(rows),raw,flush=True)
 # Reuse the completed source-runtime scan and exact compact dependency records.
 runtime_paths=old['prior_audit_sources']+[dict(path=str((R/e['directory']/(n+'.json.gz')).relative_to(R)),sha256=oldpins[str((R/e['directory']/(n+'.json.gz')).relative_to(R))]['sha256']) for e in old['audits'] for n in e['producers']]
 for e in runtime_paths:
  f=R/e['path'];assert sha(f)==e['sha256'];assert f.stat().st_size<=16*(1<<20)
  with gzip.open(f,'rb') as stream:raw=stream.read(256*(1<<20)+1)
  assert len(raw)<=256*(1<<20)
  for r in json.loads(raw):
   row=dict(kind=r['kind'],references=r['references'])
   if r['name'] in runtime_rows:assert runtime_rows[r['name']]==row
   else:runtime_rows[r['name']]=row
 banned={'GenericForest.ScalarBits.decode','GenericForest.ScalarBits.encode','OrdinaryDispatch.commonFresh','OrdinaryCommonSplit.Source.labelMax','OrdinaryCommonSplit.marked','OrdinaryCommonSplit.relabel','OrdinaryCommonSplit.swap'}|{'GenericForest.BinaryProvider.'+x for x in ['labelValue','blockValue','forestValue','treeValue','sourcesValue','targetValue','forestOptionValue']}
 def scan(starts,records):
  seen=set();boundary=set();todo=list(starts)
  while todo:
   n=todo.pop()
   if n in seen:continue
   assert n not in banned,('BANNED_RUNTIME_REFERENCE',n);seen.add(n);r=records.get(n)
   if r is None:boundary.add(n);continue
   if r['kind']=='theorem':continue
   todo.extend(r['references'])
  return seen,boundary
 try:scan(['plant'],{'plant':dict(kind='definition',references=['GenericForest.ScalarBits.decode'])})
 except AssertionError:rec['controls']['runtime_decode_injection']='CAUGHT_BY_SAME_SCAN'
 else:raise AssertionError('RUNTIME_PROJECTION_PLANT_SURVIVED')
 roots=['OrdinaryDispatch.StoredNumeric.'+n for n in ['maximumCopy','maximumBlock','freshOne','freshPair','swapCopy','relabelSwap','markedBits','leafEqual','contractBits','contractPairBits','commonPayloadBits']]
 seen,boundary=scan(roots,runtime_rows)
 assert not any(n.startswith(('OrdinaryDispatch.','GenericForest.','Universal233.','RMAF.')) for n in boundary),sorted(boundary)
 rec['runtime_scan']=dict(registered=roots,visited=sorted(seen),standard_boundary=sorted(boundary),nativeIR='OPEN',scope='Stored nonproof body reference scan; no mathematical encode/decode/treeValue/source marker conversions')
 assert axioms<=A.ALLOWED
 for e in rec['sources']:assert sha(R/e['source'])==e['source_sha256'] and sha(R/e['olean'])==e['olean_sha256']
 for p,h in rec['inputs'].items():assert sha(R/p)==h
 rec.update(status='PASS_AUTHOR_FINITE_BIT_FRESH_STORED_WIDTH_AUDIT',owned_modules=len(own),actual_imported_modules=len(order),owned_stored_occurrences=stored,axiom_union=sorted(axioms),new_compressed_bytes=total,all_new_proof_bodies_retained=False,all_new_nonproof_bodies_retained=True,actual_full_proof_reference_axiom_walk=True,original_metadata_preserved=True)
 save();print(rec['status'],len(order),stored,flush=True)
except BaseException as e:rec.update(status='FAILED_NOT_ACCEPTED',error=repr(e));save();raise
